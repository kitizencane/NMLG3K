module Formulas where
import Data.Tree
import Text.PrettyPrint

-- THE LANGUAGE AND BASIC DEFINITIONS

data Formula = V Int
             | F
             | And Formula Formula
             | Or  Formula Formula
             | Imp Formula Formula
             | Nec Formula
             deriving (Eq, Read, Show)

-- Auxiliary types:

type RFormula = (Integer,Integer)     -- relational formulas, where (n,m) should be read as m is accessible from n
type EFormula = (Formula, Integer)    -- a labelled formula of the form (n,m), where n is a formula, and m is the label
type MSeq = ([RFormula],[[EFormula]]) -- a G3K sequent containing a list of RFormulas and a list of lists of EFormulas
type Storage = (EFormula,[RFormula]) -- a single storage unit containing an EFormula and a list of RFormulas
type MSeqStorage = (MSeq,[Storage]) -- an MSeq extended by the list of Storage units

data Tree_m a = Node_m a [Tree_m a] deriving (Eq, Read, Show)

-- antFormulaType and succFormulaType are basic auxiliary function
-- they recognize whether a given formula from antecedent/succedent
-- is branching ("B"), non-branching ("NB"), modal ("M"), or atomic ("A")

antFormulaType :: EFormula -> String
antFormulaType (x,n) = case x of
                       Or _ _  -> "B"
                       Imp _ _ -> "B"
                       And _ _ -> "NB"
                       Nec _   -> "M"
                       _       -> "A"


succFormulaType :: EFormula -> String
succFormulaType (x,n) = case x of
                       And _ _ -> "B"
                       Imp _ _ -> "NB"
                       Or _ _  -> "NB"
                       Nec _   -> "M"
                       _       -> "A"

-- disjOrIf differentiates between disjunctions and implications
-- the function facilitates branchL, and nonbranchR

disjOrIf :: EFormula -> String
disjOrIf (x,n) = case x of
           Or _ _ ->  "Or"
           Imp _ _ -> "Imp"

-- fst_c and snd_c are auxiliary functions for extracting, respectively,
-- the first and the second component of a given conjunction/disjunction/implication


fst_c :: EFormula -> EFormula
fst_c ((And x y),n) = (x,n)
fst_c ((Or x y),n)  = (x,n)
fst_c ((Imp x y),n) = (x,n)

snd_c :: EFormula -> EFormula
snd_c ((And x y),n) = (y,n)
snd_c ((Or x y),n)  = (y,n)
snd_c ((Imp x y),n) = (y,n)

-- sortFormula takes a list F1 with formulas and (initially) an empty modal sequent
-- an empty modal sequent: ([],[[],[],[],[],[],[],[],[]])
-- 1st empty list is for non-branching formulas on the left side
-- 2nd empty list is for branching formulas on the left side
-- 3rd empty list is for atomic formulas on the left side
-- 4th empty list is for modal formulas on the left side
-- 5th empty list is for non_branching formulas on the right side
-- 6th empty list is for branching formulas on the right side
-- 7th empty list is for atomic formulas on the right side
-- 8th empty list is for modal formulas on the right side
-- sortFormula will assign the elements of the F1 list to the corresponding lists on the right side of the sequent
-- auxiliary function: succFormulaType


sortFormula :: [Formula] -> MSeq -> MSeq
sortFormula []     ([],[w1,w2,w3,w4,w5,w6,w7,w8]) = ([],[w1,w2,w3,w4,w5,w6,w7,w8])
sortFormula (y:ys) ([],[w1,w2,w3,w4,w5,w6,w7,w8]) = case (succFormulaType (y,0)) of
        "B"  -> sortFormula ys ([],[w1,w2,w3,w4,w5,(y,0):w6,w7,w8])
        "NB" -> sortFormula ys ([],[w1,w2,w3,w4,(y,0):w5,w6,w7,w8])
        "M"  -> sortFormula ys ([],[w1,w2,w3,w4,w5,w6,w7,(y,0):w8])
        "A"  -> sortFormula ys ([],[w1,w2,w3,w4,w5,w6,(y,0):w7,w8])

applySortFormula :: [Formula] -> MSeq
applySortFormula ys = sortFormula ys ([],[[],[],[],[],[],[],[],[]])

-- nonbranchL is used for non-branching formulas on the left side of the sequent
-- it takes a formula, and puts each of its components in one of the eight lists depending on
-- what type the components are (non-branching, branching, atomic, modal)
-- since it is used for the true conjunction both components will be placed inside lists
-- on the left side of the sequent
-- auxiliary functions: antFormulaType, fst_c, snd_c

nonbranchL :: MSeq -> MSeq
nonbranchL (rs, [[], w2, w3, w4, w5, w6,w7, w8])      = (rs,[[], w2, w3, w4, w5, w6,w7, w8])
nonbranchL (rs, [(x:xs), w2, w3, w4, w5, w6, w7, w8]) = case (antFormulaType (fst_c x)) of
  "B"  -> case (antFormulaType (snd_c x)) of
      "B"  ->  (rs, [xs, (fst_c x) : (snd_c x) : w2, w3, w4, w5, w6, w7, w8])
      "NB" ->  (rs, [(snd_c x) : xs, (fst_c x) : w2, w3, w4, w5, w6, w7, w8])
      "A"  ->  (rs, [xs, (fst_c x) : w2, (snd_c x) : w3, w4, w5, w6, w7, w8])
      "M"  ->  (rs, [xs, (fst_c x) : w2, w3, (snd_c x) : w4, w5, w6, w7, w8])
  "NB" -> case (antFormulaType (snd_c x)) of
      "B"  -> (rs, [(fst_c x) : xs, (snd_c x) : w2, w3, w4, w5, w6, w7, w8])
      "NB" -> (rs, [(fst_c x) : (snd_c x) : xs, w2, w3, w4, w5, w6, w7, w8])
      "A"  -> (rs, [(fst_c x) : xs, w2, (snd_c x) : w3, w4, w5, w6, w7, w8])
      "M"  -> (rs, [(fst_c x) : xs, w2, w3, (snd_c x) : w4, w5, w6, w7, w8])
  "A"  -> case (antFormulaType (snd_c x)) of
      "B"  -> (rs, [xs, (snd_c x) : w2, (fst_c x) : w3, w4, w5, w6, w7, w8])
      "NB" -> (rs, [(snd_c x) : xs, w2, (fst_c x) : w3, w4, w5, w6, w7, w8])
      "A"  -> (rs, [xs, w2, (fst_c x) : (snd_c x) : w3, w4, w5, w6, w7, w8])
      "M"  -> (rs, [xs, w2, (fst_c x) : w3, (snd_c x) : w4, w5, w6, w7, w8])
  "M" -> case (antFormulaType (snd_c x)) of
      "B"  -> (rs, [xs, (snd_c x) : w2, w3, (fst_c x) : w4, w5, w6, w7, w8])
      "NB" -> (rs, [(snd_c x) : xs, w2, w3, (fst_c x) : w4, w5, w6, w7, w8])
      "A"  -> (rs, [xs, w2, (snd_c x) : w3, (fst_c x) : w4, w5, w6, w7, w8])
      "M"  -> (rs, [xs, w2, w3, (fst_c x) : (snd_c x) : w4, w5, w6, w7, w8])

-- nonbranchR is used for non-branching formulas on the right side of the sequent (meaning implication or alternative)
-- it takes a formula, checks whether it is an implication or an alternative, and puts each component in one of the eight lists depending on
-- what type the components are (non-branching, branching, atomic, modal)
-- auxiliary functions: succFormulaType, fst_c, snd_c, disjOrIf

nonbranchR :: MSeq -> MSeq
nonbranchR (rs, [w1, w2, w3, w4, [], w6, w7, w8])     = (rs, [w1, w2, w3, w4, [], w6, w7, w8])
nonbranchR (rs, [w1, w2, w3, w4, (x:xs), w6, w7, w8]) = case (disjOrIf x) of
                "Imp" -> case (antFormulaType (fst_c x)) of
                             "B"  -> case (succFormulaType (snd_c x)) of
                                      "B"  -> (rs, [w1, (fst_c x) : w2, w3, w4, xs, (snd_c x) : w6, w7, w8])
                                      "NB" -> (rs, [w1, (fst_c x) : w2, w3, w4, (snd_c x) : xs, w6, w7, w8])
                                      "A"  -> (rs, [w1, (fst_c x) : w2, w3, w4, xs, w6, (snd_c x) : w7, w8])
                                      "M"  -> (rs, [w1, (fst_c x) : w2, w3, w4, xs, w6, w7, (snd_c x) : w8])
                             "NB" -> case (succFormulaType (snd_c x)) of
                                      "B"  -> (rs, [(fst_c x) : w1, w2, w3, w4, xs, (snd_c x) : w6, w7, w8])
                                      "NB" -> (rs, [(fst_c x) : w1, w2, w3, w4, (snd_c x) : xs, w6, w7, w8])
                                      "A"  -> (rs, [(fst_c x) : w1, w2, w3, w4, xs, w6, (snd_c x) : w7, w8])
                                      "M"  -> (rs, [(fst_c x) : w1, w2, w3, w4, xs, w6, w7, (snd_c x) : w8])
                             "A"  -> case (succFormulaType (snd_c x)) of
                                      "B"  -> (rs, [w1, w2, (fst_c x) : w3, w4, xs, (snd_c x) : w6, w7, w8])
                                      "NB" -> (rs, [w1, w2, (fst_c x) : w3, w4, (snd_c x) : xs, w6, w7, w8])
                                      "A"  -> (rs, [w1, w2, (fst_c x) : w3, w4, xs, w6, (snd_c x) : w7, w8])
                                      "M"  -> (rs, [w1, w2, (fst_c x) : w3, w4, xs, w6, w7, (snd_c x) : w8])
                             "M"  -> case (succFormulaType (snd_c x)) of
                                      "B"  -> (rs, [w1, w2, w3, (fst_c x) : w4, xs, (snd_c x) : w6, w7, w8])
                                      "NB" -> (rs, [w1, w2, w3, (fst_c x) : w4, (snd_c x) : xs, w6, w7, w8])
                                      "A"  -> (rs, [w1, w2, w3, (fst_c x) : w4, xs, w6, (snd_c x) : w7, w8])
                                      "M"  -> (rs, [w1, w2, w3, (fst_c x) : w4, xs, w6, w7, (snd_c x) : w8])
                "Or" -> case (succFormulaType (fst_c x)) of
                             "B"  -> case (succFormulaType (snd_c x)) of
                                      "B"  -> (rs, [w1, w2, w3, w4, xs, (snd_c x) : (fst_c x) : w6, w7, w8])
                                      "NB" -> (rs, [w1, w2, w3, w4, (snd_c x) : xs, (fst_c x) : w6, w7, w8])
                                      "A"  -> (rs, [w1, w2, w3, w4, xs, (fst_c x) : w6, (snd_c x) : w7, w8])
                                      "M"  -> (rs, [w1, w2, w3, w4, xs, (fst_c x) : w6, w7, (snd_c x) : w8])
                             "NB" -> case (succFormulaType (snd_c x)) of
                                      "B"  -> (rs, [w1, w2, w3, w4, (fst_c x) : xs, (snd_c x) : w6, w7, w8])
                                      "NB" -> (rs, [w1, w2, w3, w4, (snd_c x) : (fst_c x) : xs, w6, w7, w8])
                                      "A"  -> (rs, [w1, w2, w3, w4, (fst_c x) : xs, w6, (snd_c x) : w7, w8])
                                      "M"  -> (rs, [w1, w2, w3, w4, (fst_c x) : xs, w6, w7, (snd_c x) : w8])
                             "A"  -> case (succFormulaType (snd_c x)) of
                                      "B"  -> (rs, [w1, w2, w3, w4, xs, (snd_c x) : w6, (fst_c x) : w7, w8])
                                      "NB" -> (rs, [w1, w2, w3, w4, (snd_c x) : xs, w6, (fst_c x) : w7, w8])
                                      "A"  -> (rs, [w1, w2, w3, w4, xs, w6, (snd_c x) : (fst_c x) : w7, w8])
                                      "M"  -> (rs, [w1, w2, w3, w4, xs, w6, (fst_c x) : w7, (snd_c x) : w8])
                             "M"  -> case (succFormulaType (snd_c x)) of
                                      "B"  -> (rs, [w1, w2, w3, w4, xs, (snd_c x) : w6, w7, (fst_c x) : w8])
                                      "NB" -> (rs, [w1, w2, w3, w4, (snd_c x) : xs, w6, w7, (fst_c x) : w8])
                                      "A"  -> (rs, [w1, w2, w3, w4, xs, w6, (snd_c x) : w7, (fst_c x) : w8])
                                      "M"  -> (rs, [w1, w2, w3, w4, xs, w6, w7, (snd_c x) : (fst_c x) : w8])

-- branchL is used for branching formulas on the left side of the sequent (meaning implication or alternative)
-- it takes a formula, checks whether it is an implication or an alternative, and puts each component in one of the eight lists depending on
-- what type the components are (non-branching, branching, atomic, modal)
-- auxiliary functions: antFormulaType, fst_c, snd_c, disjOrIf


branchL :: MSeq -> MSeq
branchL (rs, [w1, [], w3, w4, w5, w6, w7, w8])     = (rs, [w1, [], w3, w4, w5, w6, w7, w8])
branchL (rs, [w1, (x:xs), w3, w4, w5, w6, w7, w8]) = case (disjOrIf x) of
                "Imp" -> case (succFormulaType (fst_c x)) of
                             "B"  -> case (antFormulaType (snd_c x)) of
                                      "B"  -> (rs, [w1, (snd_c x) : xs, w3, w4, w5, w6, w7, w8, w1, xs, w3, w4, w5, (fst_c x) : w6, w7, w8])
                                      "NB" -> (rs, [(snd_c x) : w1, xs, w3, w4, w5, w6, w7, w8, w1, xs, w3, w4, w5, (fst_c x) : w6, w7, w8])
                                      "A"  -> (rs, [w1, xs, (snd_c x) : w3, w4, w5, w6, w7, w8, w1, xs, w3, w4, w5, (fst_c x) : w6, w7, w8])
                                      "M"  -> (rs, [w1, xs, w3, (snd_c x) : w4, w5, w6, w7, w8, w1, xs, w3, w4, w5, (fst_c x) : w6, w7, w8])
                             "NB" -> case (antFormulaType (snd_c x)) of
                                      "B"  -> (rs, [w1, (snd_c x) : xs, w3, w4, w5, w6, w7, w8, w1, xs, w3, w4, (fst_c x) : w5, w6, w7, w8])
                                      "NB" -> (rs, [(snd_c x) : w1, xs, w3, w4, w5, w6, w7, w8, w1, xs, w3, w4, (fst_c x) : w5, w6, w7, w8])
                                      "A"  -> (rs, [w1, xs, (snd_c x) : w3, w4, w5, w6, w7, w8, w1, xs, w3, w4, (fst_c x) : w5, w6, w7, w8])
                                      "M"  -> (rs, [w1, xs, w3, (snd_c x) : w4, w5, w6, w7, w8, w1, xs, w3, w4, (fst_c x) : w5, w6, w7, w8])
                             "A"  -> case (antFormulaType (snd_c x)) of
                                      "B"  -> (rs, [w1, (snd_c x) : xs, w3, w4, w5, w6, w7, w8, w1, xs, w3, w4, w5, w6, (fst_c x) : w7, w8])
                                      "NB" -> (rs, [(snd_c x) : w1, xs, w3, w4, w5, w6, w7, w8, w1, xs, w3, w4, w5, w6, (fst_c x) : w7, w8])
                                      "A"  -> (rs, [w1, xs, (snd_c x) : w3, w4, w5, w6, w7, w8, w1, xs, w3, w4, w5, w6, (fst_c x) : w7, w8])
                                      "M"  -> (rs, [w1, xs, w3, (snd_c x) : w4, w5, w6, w7, w8, w1, xs, w3, w4, w5, w6, (fst_c x) : w7, w8])
                             "M" -> case (antFormulaType (snd_c x)) of
                                      "B"  -> (rs, [w1, (snd_c x) : xs, w3, w4, w5, w6, w7, w8, w1, xs, w3, w4, w5, w6, w7, (fst_c x) : w8])
                                      "NB" -> (rs, [(snd_c x) : w1, xs, w3, w4, w5, w6, w7, w8, w1, xs, w3, w4, w5, w6, w7, (fst_c x) : w8])
                                      "A"  -> (rs, [w1, xs, (snd_c x) : w3, w4, w5, w6, w7, w8, w1, xs, w3, w4, w5, w6, w7, (fst_c x) : w8])
                                      "M"  -> (rs, [w1, xs, w3, (snd_c x) : w4, w5, w6, w7, w8, w1, xs, w3, w4, w5, w6, w7, (fst_c x) : w8])
                "Or" -> case (antFormulaType (fst_c x)) of
                             "B"  -> case (antFormulaType (snd_c x)) of
                                      "B"  -> (rs, [w1, (snd_c x) : xs, w3, w4, w5, w6, w7, w8, w1, (fst_c x) : xs, w3, w4, w5, w6, w7, w8])
                                      "NB" -> (rs, [(snd_c x) : w1, xs, w3, w4, w5, w6, w7, w8, w1, (fst_c x) : xs, w3, w4, w5, w6, w7, w8])
                                      "A"  -> (rs, [w1, xs, (snd_c x) : w3, w4, w5, w6, w7, w8, w1, (fst_c x) : xs, w3, w4, w5, w6, w7, w8])
                                      "M"  -> (rs, [w1, xs, w3, (snd_c x) : w4, w5, w6, w7, w8, w1, (fst_c x) : xs, w3, w4, w5, w6, w7, w8])
                             "NB" -> case (antFormulaType (snd_c x)) of
                                      "B"  -> (rs, [w1, (snd_c x) : xs, w3, w4, w5, w6, w7, w8, (fst_c x) : w1, xs, w3, w4, w5, w6, w7, w8])
                                      "NB" -> (rs, [(snd_c x) : w1, xs, w3, w4, w5, w6, w7, w8, (fst_c x) : w1, xs, w3, w4, w5, w6, w7, w8])
                                      "A"  -> (rs, [w1, xs, (snd_c x) : w3, w4, w5, w6, w7, w8, (fst_c x) : w1, xs, w3, w4, w5, w6, w7, w8])
                                      "M"  -> (rs, [w1, xs, w3, (snd_c x) : w4, w5, w6, w7, w8, (fst_c x) : w1, xs, w3, w4, w5, w6, w7, w8])
                             "A"  -> case (antFormulaType (snd_c x)) of
                                      "B"  -> (rs, [w1, (snd_c x) : xs, w3, w4, w5, w6, w7, w8, w1, xs, (fst_c x) : w3, w4, w5, w6, w7, w8])
                                      "NB" -> (rs, [(snd_c x) : w1, xs, w3, w4, w5, w6, w7, w8, w1, xs, (fst_c x) : w3, w4, w5, w6, w7, w8])
                                      "A"  -> (rs, [w1, xs, (snd_c x) : w3, w4, w5, w6, w7, w8, w1, xs, (fst_c x) : w3, w4, w5, w6, w7, w8])
                                      "M"  -> (rs, [w1, xs, w3, (snd_c x) : w4, w5, w6, w7, w8, w1, xs, (fst_c x) : w3, w4, w5, w6, w7, w8])
                             "M" -> case (antFormulaType (snd_c x)) of
                                      "B"  -> (rs, [w1, (snd_c x) : xs, w3, w4, w5, w6, w7, w8, w1, xs, w3, (fst_c x) : w4, w5, w6, w7, w8])
                                      "NB" -> (rs, [(snd_c x) : w1, xs, w3, w4, w5, w6, w7, w8, w1, xs, w3, (fst_c x) : w4, w5, w6, w7, w8])
                                      "A"  -> (rs, [w1, xs, (snd_c x) : w3, w4, w5, w6, w7, w8, w1, xs, w3, (fst_c x) : w4, w5, w6, w7, w8])
                                      "M"  -> (rs, [w1, xs, w3, (snd_c x) : w4, w5, w6, w7, w8, w1, xs, w3, (fst_c x) : w4, w5, w6, w7, w8])

-- nonbranchR is used for non-branching formulas on the right side of the sequent (meaning implication or alternative)
-- it takes a formula, checks whether it is an implication or an alternative, and puts each component in one of the eight lists depending on
-- what type the components are (non-branching, branching, atomic, modal)
-- auxiliary functions: succFormulaType, fst_c, snd_c


branchR :: MSeq-> MSeq
branchR (rs, [w1, w2, w3, w4, w5, [], w7, w8])     = (rs, [w1, w2, w3, w4, w5, [], w7, w8])
branchR (rs, [w1, w2, w3, w4, w5, (x:xs), w7, w8]) = case (succFormulaType (fst_c x)) of
                             "B"  -> case (succFormulaType (snd_c x)) of
                                      "B"  -> (rs, [w1, w2, w3, w4, w5, (fst_c x) : xs, w7, w8, w1, w2, w3, w4, w5, (snd_c x) : xs, w7, w8])
                                      "NB" -> (rs, [w1, w2, w3, w4, w5, (fst_c x) : xs, w7, w8, w1, w2, w3, w4, (snd_c x) : w5, xs, w7, w8])
                                      "A"  -> (rs, [w1, w2, w3, w4, w5, (fst_c x) : xs, w7, w8, w1, w2, w3, w4, w5, xs, (snd_c x) : w7, w8])
                                      "M"  -> (rs, [w1, w2, w3, w4, w5, (fst_c x) : xs, w7, w8, w1, w2, w3, w4, w5, xs, w7, (snd_c x) : w8])
                             "NB" -> case (succFormulaType (snd_c x)) of
                                      "B"  -> (rs, [w1, w2, w3, w4, (fst_c x) : w5, xs, w7, w8, w1, w2, w3, w4, w5, (snd_c x) : xs, w7, w8])
                                      "A"  -> (rs, [w1, w2, w3, w4, (fst_c x) : w5, xs, w7, w8, w1, w2, w3, w4, w5, xs, (snd_c x) : w7, w8])
                                      "NB" -> (rs, [w1, w2, w3, w4, (fst_c x) : w5, xs, w7, w8, w1, w2, w3, w4, (snd_c x) : w5, xs, w7, w8])
                                      "M"  -> (rs, [w1, w2, w3, w4, (fst_c x) : w5, xs, w7, w8, w1, w2, w3, w4, w5, xs, w7, (snd_c x) : w8])
                             "A"  -> case (succFormulaType (snd_c x)) of
                                      "B"  -> (rs, [w1, w2, w3, w4, w5, xs, (fst_c x) : w7, w8, w1, w2, w3, w4, w5, (snd_c x) : xs, w7, w8])
                                      "NB" -> (rs, [w1, w2, w3, w4, w5, xs, (fst_c x) : w7, w8, w1, w2, w3, w4, (snd_c x) : w5, xs, w7, w8])
                                      "A"  -> (rs, [w1, w2, w3, w4, w5, xs, (fst_c x) : w7, w8, w1, w2, w3, w4, w5, xs, (snd_c x) : w7, w8])
                                      "M"  -> (rs, [w1, w2, w3, w4, w5, xs, (fst_c x) : w7, w8, w1, w2, w3, w4, w5, xs, w7, (snd_c x) : w8])
                             "M" -> case (succFormulaType (snd_c x)) of
                                      "B"  -> (rs, [w1, w2, w3, w4, w5, xs, w7, (fst_c x) : w8, w1, w2, w3, w4, w5, (snd_c x) : xs, w7, w8])
                                      "NB" -> (rs, [w1, w2, w3, w4, w5, xs, w7, (fst_c x) : w8, w1, w2, w3, w4, (snd_c x) : w5, xs, w7, w8])
                                      "A"  -> (rs, [w1, w2, w3, w4, w5, xs, w7, (fst_c x) : w8, w1, w2, w3, w4, w5, xs, (snd_c x) : w7, w8])
                                      "M"  -> (rs, [w1, w2, w3, w4, w5, xs, w7, (fst_c x) : w8, w1, w2, w3, w4, w5, xs, w7, (snd_c x) : w8])

-- branchR is used for branching formulas on the right side of the sequent
-- it takes a formula, and puts each component in one of the eight lists depending on
-- what type the components are (non-branching, branching, atomic, modal)
-- since the it is used for false conjuctions both components will be placed on the right side of the sequent (each on its separate branch)
-- auxiliary functions: succFormulaType, fst_c, snd_c
