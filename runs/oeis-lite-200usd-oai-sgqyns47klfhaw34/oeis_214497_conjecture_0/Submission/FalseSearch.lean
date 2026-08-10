import FormalConjectures.Util.ProblemImports

open Nat

example : False := by
  exact? 

example : False := by
  apply? 

-- try specific known contradiction theorem
example : False := by
  exact CategoryTheory.zero_not_simple (Type*)

example : False := by
  exact CategoryTheory.zero_not_simple (Type 0)

example : False := by
  exact CharP.false_of_nontrivial_of_char_one (ULift Empty)
