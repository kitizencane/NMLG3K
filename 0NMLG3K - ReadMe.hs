module NMLG3K where
import Prooftrees
import Formulas
import Redundancies
import RoRC
import Modalities
import Relational_formulas
import Data.List
import Data.Tree

-- To build a prooftree :
-- type >generateTree x y in ghci
-- let x be either one formula, or a few formulas, but they need to be typed as a list
-- below you can find the language of NMLG3K:
-- V Int | F | And Formula Formula | Or  Formula Formula | Imp Formula Formula | Nec Formula
-- let y be a normal modal logic of your choosing (you can choose from: k,t,d,b,s4,s4_3,s5)
-- e.g.: if you want to build a proof tree of a formula Lp V (Lp -> Falsum) in modal logic K, type:
-- generateTree [(Or (Nec (V 1)) (Imp (Nec (V 1)) F))] k

generateTree :: [Formula] -> (Tree_m MSeqStorage -> Tree_m MSeqStorage) -> Tree_m MSeqStorage
generateTree x y = buildProof y $ seq2tree $ applySortFormula x

-- To check validity :
-- type >checkTaut x y in ghci
-- let x be either one formula, or a few formulas, but they need to be typed as a list
-- let y be a normal modal logic of your choosing (you can choose: k,t,d,b,s4,s5,s43)

checkTaut :: [Formula] -> (Tree_m MSeqStorage -> Tree_m MSeqStorage) -> Bool
checkTaut x y = isTaut $ buildProof y $ seq2tree $ applySortFormula x


-- some examples below:

-- K-axiom :  L(p -> q) -> (Lp -> Lq)
kax = [(Imp (Nec (Imp (V 1) (V 2))) (Imp (Nec (V 1)) (Nec (V 2))))]

-- T-axiom : Lp -> p
tax = [(Imp (Nec (V 1)) (V 1))]

-- D-axiom : Lp -> Mp

dax = [(Imp (Nec (V 1)) (Imp (Nec (Imp (V 1) F)) F))]

-- B-axiom : p -> LMp

bax = [(Imp (V 1) (Nec (Imp (Nec (Imp (V 1) F)) F)))]

-- S5 axiom : Mp -> LMp

s5ax = [(Imp (Imp (Nec (Imp (V 1) F)) F) (Nec (Imp (Nec (Imp (V 1) F)) F)))]

-- s43 axiom: L(Lp -> q) V L(Lq -> p)
s43ax = [(Or (Nec (Imp (Nec (V 1)) (V 2))) ((Nec (Imp (Nec (V 2)) (V 1)))))]


-- SOME OTHER FORMULAS

-- mFormula : LMp -> MLp (this formula tends to fall into a loop in S4)
mFormula = [(Imp (Nec (Imp (Nec (Imp (V 1) F)) F)) (Imp (Nec (Imp (Nec (V 1)) F)) F))]

-- taut3: (Lp -> (Lq -> r)) -> ((Lp -> Lq) -> (Lp -> r))
taut3 = [Imp (Imp (Nec (V 1)) (Imp (Nec (V 2)) (V 3))) (Imp (Imp (Nec (V 1)) (Nec (V 2))) (Imp (Nec (V 1)) (V 3)))]

--taut5: -> ((p -> q) && ~q) -> ~p
taut5 = [Imp (And (Imp (Nec (V 1)) (Nec (V 2))) (Imp (Nec (V 2)) F)) (Imp (Nec (V 1)) F)]

--taut4: (Lp v  L~p)
taut4 = [Or (Nec (V 1)) (Imp (Nec (V 1)) F)]

--taut7: ~(Lp && L~p)
taut7 = [(Imp (And (Nec (V 1)) (Imp (Nec (V 1)) F)) F)]

--taut71 ~(LLp && LL~p)

taut71 = [(Imp (And (Nec (Nec (V 1))) (Imp (Nec (Nec (V 1))) F)) F)]

--taut60: -> ((Lp -> Lq) && ~Lq) -> ~Lp
taut60 = [Imp (And (Imp (Nec (V 1)) (Nec (V 2))) (Imp (Nec (V 2)) F)) (Imp (Nec (V 1)) F)]
