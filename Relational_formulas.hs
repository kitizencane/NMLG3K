module Relational_formulas where
import Formulas
import Modalities
import SetEq
import Data.List

-- A FULL LIST OF PREDEFINED RELATIONAL CLOSURES :

k :: Tree_m MSeqStorage -> Tree_m MSeqStorage
k x = x

t :: Tree_m MSeqStorage -> Tree_m MSeqStorage
t x = applyReflexive x

b :: Tree_m MSeqStorage -> Tree_m MSeqStorage
b x = applySymmetric x

d :: Tree_m MSeqStorage -> Tree_m MSeqStorage
d x = applySerial x

s4 :: Tree_m MSeqStorage -> Tree_m MSeqStorage
s4 x = applyTransitive $ applyReflexive x

s4_3 :: Tree_m MSeqStorage -> Tree_m MSeqStorage
s4_3 x = applys43Main $ s4 x

s5 :: Tree_m MSeqStorage -> Tree_m MSeqStorage
s5 x = applyEuclidean $ b x


-- S4.3 CLOSURE -------
-- *- this section is quite unfortunately called s4.3. closure
-- in effect, the functions below allow s4.3. closure
-- but themselves, they portray the connectedness rule

{- applys43Main :: Tree_m MSeqStorage -> Tree_m MSeqStorage
applys43Main (Node_m ((rs,s),ms) []) = applys43Aux (s43 rs)
                                        (Node_m ((rs,s),ms) [])
applys43Main (Node_m ((rs,xs),ms) zs) = (Node_m ((rs,xs),ms) (map applys43Main zs))
 -}

-- applys43Main executes an s43 closure on a leaf of a tree
-- auxiliary function: applys43Aux, s43, nonReps43

applys43Main :: Tree_m MSeqStorage -> Tree_m MSeqStorage
applys43Main (Node_m ((rs,s),ms) []) = applys43Aux (nonReps43 (s43 rs) rs)
                                        (Node_m ((rs,s),ms) [])
applys43Main (Node_m ((rs,xs),ms) zs) = (Node_m ((rs,xs),ms) (map applys43Main zs))

-- applys43Aux takes a list of RFormulas and a leaf of a tree
-- the list of RFormulas is meant to be a list of euclidean succedent
-- (compare how it's consequently applied in applyS43Main)
-- for any element of the list of RFormulas it will create two parallel sub-nodes
-- one of which will be an original sequent, with an euclidean succedent added
-- the other node will contain the euclidean succedent reversed
-- effectively, it corresponds to the connectedness rule, as below:
-- 0R1 && 0R2 -> 1R2 || 2R1


applys43Aux :: [RFormula] -> Tree_m MSeqStorage -> Tree_m MSeqStorage
applys43Aux [] (Node_m ((rs,s),ms) [])          = (Node_m ((rs,s),ms) [])
applys43Aux ((x,y):xs) (Node_m ((rs,s),ms) [])  = applys43Aux xs (Node_m ((rs,s),ms)
                                                  [(Node_m ((rs ++ [(x,y)],s),ms) []),
                                                  (Node_m ((rs ++ [(y,x)],s),ms) [])])
applys43Aux xs (Node_m ((rs,s),ms) zs)          = (Node_m ((rs,s),ms) (map (applys43Aux xs) zs))

-- s43 out of list of RFormulas finds all pairs of relational formulas
-- complying to the pattern of euclideaness axiom's antecedent
-- and returns a list of euclidean succedents

s43 :: [RFormula] -> [RFormula]
s43 xs = [euclSucc x y | x <- xs, y <- xs
         , areEuclidean x y]

-- nonReps43 prevents redundant closures

nonReps43 :: [RFormula] -> [RFormula]-> [RFormula]
nonReps43 [] rs = []
nonReps43 xs rs = [(a,b) | (a,b) <- xs, not ((a,b) `elem` rs), not ((b,a) `elem` rs)]


--- REFLEXIVITY
-- applyReflexive collects all labels ascribed to all Formulas
-- flattens them to a list of integers
-- then creates a reflexive pair for every integer
-- consequently, new reflexive pairs are adjoined
-- to a list of relational formulas
-- auxiliary functions: collectLabels, refPairs, rmDupl, nonRep

applyReflexive :: Tree_m MSeqStorage -> Tree_m MSeqStorage
applyReflexive (Node_m ((rs,xs),ms) []) = (Node_m ((f ++ rs, xs),ms) [])
                                           where
                                           f = nonRep (concat (map collectLabels xs)) rs
applyReflexive (Node_m ((rs,xs),ms) zs) = (Node_m ((rs,xs),ms) (map applyReflexive zs))

-- collectLabels out of lists of EFormulas returns a list of their labels

collectLabels :: [EFormula] -> [Integer]
collectLabels [] = []
collectLabels ((x,n) : xs) = [n] ++ collectLabels xs

--nonRep makes sure no repeated closures under reflexivity are made

nonRep :: [Integer] -> [RFormula] -> [RFormula]
nonRep [] rs     = []
nonRep xs rs = [(a,a) | a <- xs, not ((a,a) `elem` rs)]

-- refPairs takes a list of Ints (out of the flattened list of RFormulas)
-- and for each element creates a reflexive ordered pair
-- it returns a list or reflexive ordered pairs

refPairs :: [Integer] -> [RFormula]
refPairs []   = []
refPairs (x:xs) = [(x,x)] ++ refPairs xs

-- rmDupl takes a list of any elements and removes all duplicates


------------ SERIAL

-- applySerial applies serial to a leaf of a tree

applySerial :: Tree_m MSeqStorage -> Tree_m MSeqStorage
applySerial (Node_m ((rs, [w1,w2,w3,w4,w5,w6,w7,w8]),ms) []) = (Node_m ((iterate serial (rs, [w1,w2,w3,w4,w5,w6,w7,w8])
                                                               !! (length w4)),ms) [])

---- if an EFormula of label "w" is in a "blind" world (no other words are accessible from "w")
---- then create a formula (w,x) where x is a new world (succedent of the highest existing world)
---- e.g. serial ([(0,1),(0,2),(0,3)],[[],[],[],[(Nec F, 3)],[],[],[],[]]) = ([(3,4),(0,1),(0,2),(0,3)],[[],[],[],[(Nec F, 3)],[],[],[],[]])

serial :: MSeq -> MSeq
serial (rs,[w1,w2,w3,((x,n):xs),w5,w6,w7,w8])
 | anySerial rs (x,n) /= []    =  (rs,[w1,w2,w3,xs ++ [(x,n)],w5,w6,w7,w8])
 | anySerial rs (x,n) == []    =  ([(n,(succMaxWorld rs))] ++ rs,
                                  [w1,w2,w3,xs ++ [(x,n)],w5,w6,w7,w8])

-- SuccMaxWorld returns a new world (a succedent of the highest label already present in the proof)

succMaxWorld :: [RFormula] -> Integer
succMaxWorld [] = 1
succMaxWorld xs = succ (maximum (rFlat xs))

-- anySerial takes a list of existing ordered pairs representing accessibility between existing worlds and an Eformula
-- it returns a list of ordered pairs of existing worlds which are seen from the world "b" (from chosen EFormula)
-- if there are none, then it is justified to create a new world, which will be seen from "b"

anySerial :: [RFormula] -> EFormula -> [RFormula]
anySerial [] (a,b) = []
anySerial xs (a,b) = [x | x <- xs, fst x == b]

---TRANSITIVE

-- applyTransitive takes a list of RFormulas and finds all pairs that meet
-- the criteria of the antecedent of the transitivity rule, then create
-- the succedent of the transitivity rule, and joins it to the inital list
-- auxiliary functions: transitive

applyTransitive :: Tree_m MSeqStorage -> Tree_m MSeqStorage
applyTransitive (Node_m ((rs,xs),ms) []) = (Node_m ((transitive rs,xs),ms) [])
applyTransitive (Node_m ((rs,xs),ms) zs) = (Node_m ((rs,xs),ms) (map applyTransitive zs))

-- transivtive takes a list of RFormulas
-- and for every pair of RFormulas theat complies to the antecedent of the transitivity rule
-- it creates a transitive formula and adjoins in to the list of RFormulas
-- auxiliary functions: areTransitive, nonRepeated, makeTransPair

transitive :: [RFormula] -> [RFormula]
transitive xs = [makeTransPair x y | x <- xs, y <- xs,
                                     areTransitive x y,
                                     nonRepeated x y xs] ++ xs


-- nonRepeated prevents joining repetitive transitive formulas

nonRepeated :: RFormula -> RFormula -> [RFormula] -> Bool
nonRepeated a b xs = if elem (makeTransPair a b) xs then False else True

-- makeTransPair takes two RFormulas and uses them to create a transitive
-- ordered pair, as in: for (1,2) and (2,3) it will result in (1,3)

makeTransPair :: RFormula -> RFormula -> RFormula
makeTransPair (x,y) (m,n) = (x,n)

-- areTransitive takes two RFormulas (a,b) (c,d) and checks whether
-- they comply to the antecedent of the transitivity rule

areTransitive :: RFormula -> RFormula -> Bool
areTransitive x y = if snd x == fst y then True else False

--- symmetry and euclideaness are implemented in a way analogous to transitivity
----------- symmetric

applySymmetric :: Tree_m MSeqStorage -> Tree_m MSeqStorage
applySymmetric (Node_m ((rs,xs),ms) []) = (Node_m ((symmetric rs,xs),ms) [])
applySymmetric (Node_m ((rs,xs),ms) zs) = (Node_m ((rs,xs),ms) (map applySymmetric zs))

symmetric :: [RFormula] -> [RFormula]
symmetric [] = []
symmetric xs = rmDupl (inverse (head xs) : symmetric (tail xs) ++ xs)

inverse :: RFormula -> RFormula
inverse (a,b) = (b,a)

----------- EUCLIDEAN

applyEuclidean :: Tree_m MSeqStorage -> Tree_m MSeqStorage
applyEuclidean (Node_m ((rs,xs),ms) []) = (Node_m ((euclidean rs,xs),ms) [])
applyEuclidean (Node_m ((rs,xs),ms) zs) = (Node_m ((rs,xs),ms) (map applyEuclidean zs))


euclidean :: [RFormula] -> [RFormula]
euclidean xs = [euclSucc x y | x <- xs, y <- xs, areEuclidean x y] ++ xs

euclSucc :: RFormula -> RFormula -> RFormula
euclSucc (x,y) (m,n) = (y,n)

areEuclidean :: RFormula -> RFormula -> Bool
areEuclidean x y = if (fst x == fst y) && (snd x /= snd y) then True else False
