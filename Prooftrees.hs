module Prooftrees where
import Formulas
import Modalities
import Relational_formulas
import Data.List
import Redundancies
import RoRC

-- THIS MODULE CONTAINS FUNCTIONS FOR BUILDING A PROOFTREE AND FOR VALIDITY CHECKING

-- seq2tree puts a given MSeq type formula in a leaf of a rose tree
seq2tree :: MSeq -> Tree_m MSeqStorage
seq2tree x = (Node_m (x,[]) [])

-- used after having called one of the branching (branchL and branchR) functions on a tree
-- calling branchL and branchR on a sequent will result in a double sequent
-- a double sequent is an ordered pair consistinsg of a list of relational formulas and a list of 16 Eformulas
-- branch splits a double sequent into two separate branches of a tree

branch :: MSeqStorage -> [Tree_m MSeqStorage]
branch ((rs,xs),ms) = [(Node_m ((rs,(take 8 xs)),ms) []), (Node_m ((rs,(drop 8 xs)),ms) [])]



-----------------------------------P R O O F  --------------------------------------

-- logicalRules is a local function written by means of pattern matching
-- it applies  G3K logical rules (for propositional connectives and modalities)
-- the order of application of the rules is:
-- 1st : non-branching in the antecedent (left conjunction)
-- then, non-branching in the succedent (right implication, right disjunction)
-- then, branching in the antecedent (left implication, left disjunction)
-- then, branching in the succedent (right conjunction)
-- then, modal in the succedent (right neccessity)
-- finally, modal in the antecedent (left neccessity)
-- the order of the rules is forced by pattern matching
-- e.g. branchL rule won't be applied unless 1st and 5th lists are empty
-- which means, there are no non-branching rules to apply anymore
-- additionally, right after applying branchL and branchR if call branch functions
-- to split the node into two separate ones

logicalRules :: Tree_m MSeqStorage -> Tree_m MSeqStorage
logicalRules (Node_m ((rs,xs),ms) []) = case xs of
  [(y:ys), w2, w3, w4, w5, w6, w7 ,w8]     -> (Node_m ((rs,xs),ms) [(Node_m ((nonbranchL ((rmDupl rs), [(y:ys),w2,w3,w4,w5,w6,w7,w8])),ms) [])])
  [[], w2, w3, w4, (y:ys), w6, w7, w8]     -> (Node_m ((rs,xs),ms) [(Node_m ((nonbranchR ((rmDupl rs), [[],w2,w3,w4,(y:ys),w6,w7,w8])),ms) [])])
  [[], (y:ys), w3, w4, [], w6, w7, w8]     -> (Node_m ((rs,xs),ms) (branch (branchL (((rmDupl rs), [[],(y:ys),w3,w4,[],w6,w7,w8])),ms)))
  [[], [], w3, w4, [], (y:ys), w7, w8]     -> (Node_m ((rs,xs),ms) (branch (branchR (((rmDupl $ rs), [[],[],w3,w4,[],(y:ys),w7,w8])),ms)))
  [[],[],w3,w4,[],[],w7,(y:ys)]            -> (Node_m ((rs,xs),ms) [(Node_m (rightBox ((rs, [[],[],w3,w4,[],[],w7, y:ys])),ms) [])])
  [[],[],w3,(y:ys),[],[],w7,[]]            -> applyLeftBox (Node_m ((rs,xs),ms) [])
logicalRules (Node_m ((rs,xs),ms) zs) = (Node_m ((rs,xs),ms) (map logicalRules zs))

-- buildProof is the most general proof building function
-- it takes 2 arguments: a function representing a given relational closure and a sequent
-- it was written by means of pattern matching and guards
-- the first pattern represents a situation where there only propositional variables left -> it doesn't do anything with such sequent
-- the second pattern represent a situation in which there are only propositional variables AND at least modal formula in the antecedent left
-- if so, it checks three additional conditions : a) whether a sequent is an axiom b) whether it falls under rule of repeating chains conditions
-- c) whether all modalities are exhausted (the idea of an "exahusted" sequent is described in Redundancies module)
-- d) a) b) nor c) apply
-- in the first 3 cases it just returns the sequent unchanged
-- in the case d) it applies the left box (by calling logicalRules) and calls buildProof recursively
-- the third pattern represents a situation in which a sequent is anything else than the two patterns described above
-- then it will just call logicalRules on it, and then buildProof recursively
-- "c" represents closure under chosen frame conditions (e.g. let c be s4)
-- the closure is called before logicalRules is applied and everytime buildProof is called


buildProof :: (Tree_m MSeqStorage -> Tree_m MSeqStorage) -> Tree_m MSeqStorage -> Tree_m MSeqStorage
buildProof c (Node_m ((rs,[[],[],w3,[],[],[],w7,[]]),ms) [])    = (Node_m ((rs,[[],[],w3,[],[],[],w7,[]]),ms) [])
buildProof c (Node_m ((rs,[[],[],w3,(x:xs),[],[],w7,[]]),ms) [])
 | isSeqTaut ((rs,[[],[],w3,(x:xs),[],[],w7,[]]),ms)            = (Node_m ((rs,[[],[],w3,(x:xs),[],[],w7,[]]),ms) [])
 | roRC ((rs,[[],[],w3,(x:xs),[],[],w7,[]]),ms)                 = (Node_m ((rs,[[],[],w3,(x:xs),[],[],w7,[]]),ms) [])
 | (and (exhausted ((rs,[[],[],w3,(x:xs),[],[],w7,[]]),ms)))    = (Node_m ((rs,[[],[],w3,(x:xs),[],[],w7,[]]),ms) [])
 | otherwise                                                    = buildProof c (logicalRules $ c (Node_m ((rs,[[],[],w3,(x:xs),[],[],w7,[]]),ms) []))
buildProof c (Node_m ((rs,xs),ms) [])
 | isSeqTaut ((rs,xs),ms)                                       = (Node_m ((rs,xs),ms) [])
 | otherwise                                                    = buildProof c (logicalRules $ c (Node_m ((rs,xs),ms) []))
buildProof c (Node_m ((rs,xs),ms) zs)                           = (Node_m ((rs,xs),ms) (map (buildProof c) zs))



--- PROOF CHECKING ----

-- flattenTree flattens a prooftree by into a list of all its leaves
-- it omits non-leaves

flattenTree :: Tree_m MSeqStorage -> [MSeqStorage]
flattenTree (Node_m x []) = [x]
flattenTree (Node_m x xs) = (concat (map flattenTree xs))

-- isSeqTaut verifies whether a given sequent is an axiom
-- it is considered an axiom if it either has the same atomic formula in both antecedent and succedent
-- or if it contains a falsum in an antecedent

isSeqTaut :: MSeqStorage -> Bool
isSeqTaut ((rs,[w1,w2,xs,w4,w5,w6,ys,w8]),ms) = (or [(fst x) == F | x <- xs])
                                                || (or [x == y | x <- xs, y <-ys])

-- areAllTaut just maps isSeqTaut over a list of sequents (the list of leaves from a prooftree)
-- if all of them are axioms, then it will return True

areAllTaut :: [MSeqStorage] -> Bool
areAllTaut xs = and (map isSeqTaut xs)

-- isTaut takes a prooftree and returns true if it is a tautology
-- and False if it isn't

isTaut :: Tree_m MSeqStorage -> Bool
isTaut x = areAllTaut $ flattenTree x
