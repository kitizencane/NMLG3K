module Redundancies where
import Formulas
import Modalities
import Data.List
import SetEq
-- THIS MODULE CONTAINS FUNCTIONS PREVENTING UNNECESSARY APPLICATIONS OF L-BOX RULE


-- main leftBox-rule function, preventing redundant applications :
-- when it applies leftBox-rule to a given EFormula, it removes (from rs)
-- the list of possible worlds in which y was already decomposed
-- it also updates the Storage unit concerning y right after L-Box rule application
-- the contents of rs are also restores rs list to its original contents

lBoxRedund :: MSeqStorage -> MSeqStorage
lBoxRedund ((rs, [w1,w2,w3,(y:ys),w5,w6,w7,w8]),ms) = restore (leftBox ((((rmDupl rs) \\ (relationalBaseList ms y))
                                                    , [w1,w2,w3,(y:ys),w5,w6,w7,w8]))
                                                    , (updateStorage y rs (rmDupl ms)))


-- applyLeftBox just calls lBoxRedund on a sequent
-- before it does that, it checks two additional conditions:
-- there are no worlds accessible from y's label at all -> it doesn't apply the rule
-- removing Storage record of y doesn't leave any new worlds that we might
-- decompose y in -> it doesn't apply the rule
-- otherwise, it applies the rule

applyLeftBox :: Tree_m MSeqStorage -> Tree_m MSeqStorage
applyLeftBox (Node_m ((rs,[[],[],w3,(y:ys),[],[],w7,[]]),ms) [])
 | (takeTheLabel (snd y) rs) == []          = (Node_m ((rs,[[],[],w3,(ys) ++ [y],[],[],w7,[]]),ms) [])
 | (rs \\ (relationalBaseList ms y)) == []  = (Node_m ((rs,[[],[],w3,(ys) ++ [y],[],[],w7,[]]),ms) [])
 | otherwise                                = (Node_m ((rs,[[],[],w3,(y:ys),[],[],w7,[]]),ms)
                                                      [(Node_m (lBoxRedund ((rs,[[],[],w3,(y:ys),[],[],w7,[]]),ms)) [])])
applyLeftBox (Node_m ((rs,xs),ms) zs)       = (Node_m ((rs,xs),ms) (map applyLeftBox zs))


-- SOME AUXILIARY FUNCTIONS :


-- relationalBaseList compares a given formula n with a whole Storage list (x:xs)
-- if it finds in (x:xs) a record referring to n,
-- it will return the list of all the worlds n already was decomposed in
-- e.g..: relationalBaseList [((Nec F,2),[(2,3)]),((Nec (Imp (V 1) (V 2)),0),[(0,1),(0,2)]),((Nec F,0),[(0,1)])]
--                           (Nec (Imp (V 1) (V 2)),0) = [(0,1),(0,2)]

relationalBaseList :: [Storage] -> EFormula -> [RFormula]
relationalBaseList [] n     = []
relationalBaseList (x:xs) n = if n == (fst x)
                                 then (snd x)
                              else relationalBaseList xs n


-- relBase takes an EFormula (F,n) and a list of relational formulas
-- it returns the list of all the worlds accessible from n
-- e.g.: relBase (Nec F,0) [(0,1),(1,2),(0,2)] = [(0,1),(0,2)]

relBase :: EFormula -> [RFormula] -> [RFormula]
relBase (f,n) rs = [(a,b) | (a,b) <- rs, a == n]


-- adjoinStor takes an EFormula (n,a), a list or relational formulas rs, and Storage list
-- if it will find an already existing record in (x:xs) referring to (n,a)
-- it will update the list of worlds in which n was decomposed
-- if it will not find an existing record referring to (n,a)
-- it will return the Storage list unchanged

adjoinStor :: EFormula -> [RFormula] -> [Storage] -> [Storage]
adjoinStor (n,a) rs []     = []
adjoinStor (n,a) rs (x:xs) = if (n,a) == (fst x)
                               then [((n,a), ((relBase (n,a) rs)))] ++ xs
                             else (x) : (adjoinStor (n,a) rs xs)




-- updateStorage is basically an extension of adjoinStor
-- it updates an already existing memory record of an Eformula
-- but if it does not find an existing record, it will create a new one


updateStorage:: EFormula -> [RFormula] -> [Storage] -> [Storage]
updateStorage n rs xs
 | (adjoinStor n rs xs) == xs   = (n,(relBase n rs)) : xs
 | otherwise                    = adjoinStor n rs xs


-- restore, retrieve, and nonRepRetrieve warrant that once memory record of a given formula has been removed from the list
-- during L-box rule application
-- right after, the list of relational formulas is restored to its original contents

restore :: MSeqStorage -> MSeqStorage
restore ((rs, [w1,w2,w3,(y:ys),w5,w6,w7,w8]),[]) = ((rs, [w1,w2,w3,(y:ys),w5,w6,w7,w8]),[])
restore ((rs, [w1,w2,w3,(y:ys),w5,w6,w7,w8]),xs) = (((rs ++ (nonRepRetrieve xs rs))
                                                    ,[w1,w2,w3,(y:ys),w5,w6,w7,w8]),xs)

retrieve :: [Storage] -> [RFormula]
retrieve [] = []
retrieve (x:xs) = (snd x) ++ (retrieve xs)


nonRepRetrieve :: [Storage] -> [RFormula] -> [RFormula]
nonRepRetrieve [] rs     = []
nonRepRetrieve xs rs     = [x | x <- (retrieve xs), not (x `elem` rs)]


-- exhausted's objective is to verify whether all modal formulas (F,n) in the antecedent
-- have already been decomposed in all possible worlds accessible from n
-- it searches through a list w4 and verifies each formula by comparing the list of relational formulas
-- from a rs list of relational formulas it extracts a list of all worlds accessible from n (let us call it rs2)
-- then, from rs2 it substracts the memory record of (F,n)
-- if it returns an empty list, a sequent is exhausted (there are no more worlds in which (F,n) can be decomposed)
-- it verifies each sequent in the list in that manner
-- this function is later used in buildProof, where "and (exhausted x)" is used

exhausted :: MSeqStorage -> [Bool]
exhausted (([],[w1,w2,w3,w4,w5,w6,w7,w8]),[])     = [True]
exhausted (([],[w1,w2,w3,w4,w5,w6,w7,w8]),ms)     = [True]
exhausted ((rs,[w1,w2,w3,[],w5,w6,w7,w8]),ms)     = [True]
exhausted ((rs,[w1,w2,w3,(y:ys),w5,w6,w7,w8]),ms) = if (takeTheLabel (snd y) (rs \\ (relationalBaseList ms y)) == [])
                                                      then (exhausted ((rs,[w1,w2,w3,ys,w5,w6,w7,w8]),ms)) ++ [True]
                                                    else (exhausted ((rs,[w1,w2,w3,ys,w5,w6,w7,w8]),ms)) ++ [False]
