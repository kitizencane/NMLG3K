module RoRC where
import Formulas
import SetEq
import Modalities
import Relational_formulas
import Redundancies

-- THIS MODULE CONTAINS FUNCTIONS FOR THE TERMINATION PROCEDURE IN TRANSITIVE LOGICS


-- REBUILDING A SEQUENT INTO A LIST OF LISTS ARRANGED BY THEIR LABELS
-- Starting from the simplest functions:

-- mergeEFormulas takes 8 lists of EFormulas from a sequent and merges them into
-- one list of EFormulas
-- let us call it a merged sequent for later use

mergeEFormulas :: [[EFormula]] -> [EFormula]
mergeEFormulas [w1,w2,w3,w4,w5,w6,w7,w8] = w1 ++ w2 ++ w3 ++ w4


-- mergeExistent takes two arguments: a labelled formula (A,n), and a list of labelled formulas (XS)
-- the function searches through the list to find a list of lists containing formulas with label n
-- if it finds one, it will adjoin (A,n) to that list
-- if it does not find one, it will return the list XS unchanged

mergeExistent :: EFormula -> [[EFormula]] -> [[EFormula]]
mergeExistent a []     = []
mergeExistent a (x:xs) = if (snd a) == (snd (head x))
                          then (a:x):xs
                         else (x):(mergeExistent a xs)


-- orderWorlds takes a list of labelled formulas (ns), a list of lists of labelled formulas (xs)
-- (a merged sequent is meant to be used as the ns list)
-- and return the list of lists of labelled formulas
-- it takes each Formula (A,n) from ns, verifies whether xs already contains a list of formulas with n label
-- if xs does not contain such a list (calling mergeExistent on (A,n) xs) does not change anything
-- then create a new list consisting only of (A,n), and adjoin it to xs
-- however, if (calling mergeExistent on (A,n) xs) will not return xs unchanged
-- that will mean that there is already a list in xs collecting formulas with n label
-- in that case, call mergeExistent on (A,n) xs and adjoin (A,n) to its proper list
-- auxiliary function: mergeExistent

orderWorlds :: [EFormula] -> [[EFormula]] -> [[EFormula]]
orderWorlds [] xs               = xs
orderWorlds (n:ns) xs
  | (mergeExistent n xs) == xs  = orderWorlds ns ([n] : xs)
  | otherwise                   = orderWorlds ns (mergeExistent n xs)


-- extractWorlds takes a sequent and returns a list of lists of EFormulas grouped by labels
-- so, for a given sequent of the form: 0: A, 0: A -> B, 1: B => 1: B -> C, 2: D it will return the list:
-- [[2: D], [1: B, 1: B -> C], [0: A, 0: A -> B]]
-- extractWorlds makes use of a merged sequent structure
-- it calls orderWorlds on a tail of a merged sequent and a list consisting of a single list with the first formula of a merged sequent
-- it is not important which formula will be used as the head (mergeEFormulas ns)
-- orderWorlds just needs at least one lists of lists in its second argument
-- so it can compare all the other formulas from the list (tail (mergeEFormulas ns)) to something
-- auxiliary functions: mergeExistent, orderWorlds, mergeEFormulas

extractWorlds :: MSeqStorage -> [[EFormula]]
extractWorlds ((rs,ns),ss) = let
  f = (tail (mergeEFormulas ns))
  g = [[head (mergeEFormulas ns)]]
  in orderWorlds f g


-- COMPARING WHETHER THE WORLD WITH THE HIGHEST LABEL IS A DUPLICATE OF ANY OTHER POSSIBLE WORLD


-- cutLabels takes a list of labelled EFormulas and returns a list of the same formulas without labels
cutLabels :: [EFormula] -> [Formula]
cutLabels []      = []
cutLabels (x:xs)  = [fst x] ++ cutLabels xs


-- qsortLabel takes a list of lists of EFormulas (formulas with labels) and returns the same list
-- only arranged in a descending order of labels

qsortLabel :: [[EFormula]] -> [[EFormula]]
qsortLabel []     = []
qsortLabel (x:xs) = qsortLabel larger ++ [x] ++ qsortLabel smaller
                    where
                       larger  = [n | n <- xs, snd (head n) > snd (head x)]
                       smaller = [m | m <- xs, snd (head m) < snd (head x)]


-- indenticalWorlds verifies whether two lists of EFormulas contain the same formulas
-- it uses cutLabels to remove the labels, and compares if the lists make identical sets
-- (not if they are exactly identical), so neither the order, nor repetitions matter

identicalWorlds :: [EFormula] -> [EFormula] -> Bool
identicalWorlds xs ys = Set (cutLabels xs) == Set (cutLabels ys)



-- THE TERMINATION PROCEDURE

-- anyDuplicates takes a sequent as an argument
-- calls extractWorlds on it, so the result is a list of lists of labelled formula arranged by their labels
-- then finds the list of content of the newest world (head (qsortLabel (extractWorlds x))))
-- and compares (using identicalworlds) the contents of that list with the contents of all the remaing worlds
-- if it finds at least one example, it will return True and, then
-- it will verify whether the found world belongs to the same chain
-- if it does, it will recognize a repeated chain (= return True)
-- otherwise, it will return False

anyDuplicates :: MSeqStorage -> Bool
anyDuplicates x = any (identicalWorlds (head (qsortLabel (extractWorlds x))))
                              (tail (qsortLabel (extractWorlds x)))


-- isChain compares if the newest possible world "b" is accessible
-- from some other world "a"
-- such that "b" is a duplicate of "a"
-- if that is the case, then we can tell that  "a" and  "b" are a part of the same chain

isChain :: MSeqStorage -> Bool
isChain ((rs,xs),ms)
 | (a,b) `elem` rs    = True
 | otherwise          = False
                       where a = duplicateLabel ((rs,xs),ms)
                             b = maximum (rFlat rs)


-- findDuplicateLabel and duplicateLabel are two auxiliary functions
-- by means of RoRC we take the newest world and try to find its already existing duplicate
-- findDuplicateLabel and duplicateLabel find the label of that duplicate

findDuplicateLabel :: [EFormula] -> [[EFormula]] -> Integer
findDuplicateLabel xs (y:ys) = if Set (cutLabels xs) == Set (cutLabels y)
                                 then (snd (head y))
                               else findDuplicateLabel xs ys

duplicateLabel :: MSeqStorage -> Integer
duplicateLabel x = findDuplicateLabel
                   (head (qsortLabel (extractWorlds x)))
                   (tail (qsortLabel (extractWorlds x)))


-- Main Rule of Repeating Chains function
-- roRC verifies whether the newest established world is a duplicate
-- of some other, already established one
-- if so, it verifies further whether they are a part
-- of the same chain

roRC :: MSeqStorage -> Bool
roRC x = case anyDuplicates x of
  True  -> isChain x
  _     -> False
