module Modalities where
import Formulas

-- THIS MODULE CONTAINS THE FUNCTIONS REFLECTING MODAL LOGICAL RULES OF G3K

-- leftBox ----------------------------------------

-- leftBox will take modal formula (f1,n) of the w4 list (modal formulas on the left side)
-- then find whether there are other worlds that are seen from n
-- if so, it will return a list of f1 formulas without the box labelled with all the worlds that are seen from n
-- for leftBox ([0,1],[0,2])[[],[],[],[F,0],[],[],[],[]]) it will return a list [(F,1),(F,2)]
-- then it will call a sortModal_left on the list above and a sequent and assign it to its proper list based on what type of formula it is
-- auxiliary functions: sortModal_left,giveNewLabels,removeMod,takeTheLabel


leftBox :: MSeq -> MSeq
leftBox ([],xs) = ([],xs)
leftBox (rs,[w1,w2,w3,(x:xs),w5,w6,w7,w8]) =
        let f = (giveNewLabels (removeMod x) (takeTheLabel (snd x) rs))
            g = (rs, [w1,w2,w3,xs ++ [x], w5,w6,w7,w8])
        in sortModal_left f g

-- removeMod takes modal formula and returns it without the modality

removeMod :: EFormula -> EFormula
removeMod (Nec x,n) = (x,n)

-- srtmodal takes a list of EFormulas and adds it to one of the eight list in the sequent
-- based on what type of formula (non-branching, branching, atomic, modal) the head of the list is
-- it is safe to only see what the head is, because the list will always consist of the same formula with different labels
-- auxiliary functions: antFormulaType

sortModal_left :: [EFormula] -> MSeq -> MSeq
sortModal_left [] x = x
sortModal_left xs (rs,[w1,w2,w3,w4, w5,w6,w7,w8]) = case antFormulaType (head xs) of
  "B"  -> (rs, [w1, xs ++ w2, w3, w4, w5, w6, w7, w8])
  "NB" -> (rs, [xs ++ w1, w2, w3, w4, w5, w6, w7, w8])
  "A"  -> (rs, [w1, w2, xs ++ w3, w4, w5, w6, w7, w8])
  "M"  -> (rs, [w1, w2, w3, xs ++ w4, w5, w6, w7, w8])


-- isCon takes an integer (a single label) and a pair of labels
-- then checks whether that single label equals the first component of the pair
-- it is used as an auxiliary function for takeTheLabel

isCon :: Integer -> RFormula -> Bool
isCon n (x,y) = if (n == x)
                  then
                    True
                else
                  False

-- it takes a single label n, list of all pairs of labels in the proof
-- and creates a list of all single labels that are seen from n
-- for takeTheLabel 1 [(1,2),(2,3),(3,4)] it will return [2,3]

takeTheLabel :: Integer -> [RFormula] -> [Integer]
takeTheLabel n xs = [snd x | x <- xs, isCon n x]

-- takes an EFormula and a list of possible worlds (= a list of integers), then assigns said formula to all the worlds from the list
-- giveNewLabels (F,0) [1,2,3] = [(F,1),(F,2),(F,3)]

giveNewLabels :: EFormula -> [Integer] -> [EFormula]
giveNewLabels (f,n) []     = []
giveNewLabels (f,n) (x:xs) = [(f,x)] ++ giveNewLabels (f,n) xs

-- rightBox ----------------------------------------------------------------------------------------------------

-- rightBox will add a new label to the list of RFormulas
-- then call sortmodal function on any modal formulas on the right side of the sequent
-- it calls and addWorld function on a label that has been assigned to a modal formula (x,n) and n's succedent
-- meanign if a modal formula has a label 0, then it will try to create a new pair of labels (0,1)
-- if 1 is already a label then it will try to create (0,2) and it will continue that way
-- until if finds a label that has not yet been introduced

rightBox :: MSeq -> MSeq
rightBox (w0,[w1,w2,w3,w4,w5,w6,w7,[]])          = (w0,[w1,w2,w3,w4,w5,w6,w7,[]])
rightBox (w0,[w1,w2,w3,w4,w5,w6,w7, (x,n) : xs]) =
     let f = (addWorld n (succ n) w0,[w1,w2,w3,w4,w5,w6,w7,(x,n) : xs])
     in sortModal_r f

-- sortmodal for the rightbox rule works similarly to a sortf function, only before placing a formula in a proper list
-- it removes its modality and replaces its label with the most recent one

sortModal_r :: MSeq -> MSeq
sortModal_r (rs,[w1,w2,w3,w4,w5,w6,w7,[]])     = (rs,[w1,w2,w3,w4,w5,w6,w7,[]])
sortModal_r (rs,[w1,w2,w3,w4,w5,w6,w7,((Nec x, n):xs)]) = case succFormulaType (x,n) of
  "B"  -> (rs, [w1, w2, w3, w4, w5, f : w6, w7, xs])
  "NB" -> (rs, [w1, w2, w3, w4, f : w5, w6, w7, xs])
  "A"  -> (rs, [w1, w2, w3, w4, w5, w6, f : w7, xs])
  "M"  -> (rs, [w1,w2,w3,w4,w5,w6,w7, xs ++ [f]])
  where f = (newLabel (x,n) rs)


-- newLabel takes a given EFormula, and replaces its label with the most recent one

newLabel :: EFormula -> [RFormula] -> EFormula
newLabel (x,n) xs = (x, mostRecentLabel xs)

-- mostrecent label finds the world, that has been added most recently

--mostRecentLabel :: [RFormula] -> Integer
--mostRecentLabel xs = snd (last xs)

mostRecentLabel :: [RFormula] -> Integer
mostRecentLabel []     = 0
mostRecentLabel (x:xs) = maximum ([snd x] ++ [(mostRecentLabel xs)])

-- addWorld uses two Ints A and B and a list of relational formulas
-- to see whether the second Int has already been introduced in the proof
-- if it hasn't been, then addWorld creates an ordered pair out of A and B and adds it to the list
-- otherwise, it is called and recursively on A and (B+1)
-- auxiliary functions: isnewLabel

addWorld :: Integer -> Integer -> [RFormula] -> [RFormula]
addWorld a b xs = if isnewLabel b xs
                    then
                      xs ++ [(a,b)]
                  else
                      addWorld a (succ b) xs


-- rFlat flattens a list of pairs of integers

rFlat :: [RFormula] -> [Integer]
rFlat [] = []
rFlat ((a,b) : xs) = [a,b] ++ rFlat xs


-- isnewLabel takes an integer and a list of RFormulas and checks whether given
-- integer is already a part of that list.

isnewLabel :: Integer -> [RFormula] -> Bool
isnewLabel n xs = not (any (n==) (rFlat xs))


rmDupl :: Eq a => [a] -> [a]
rmDupl [] = []
rmDupl (x:xs) = if (elem x xs) then rmDupl xs else x : rmDupl xs
