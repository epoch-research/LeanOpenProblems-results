import FormalConjectures.Util.ProblemImports

open Lean Elab Term

elab "sidonBug" : term => do
  let base := `_private.FormalConjecturesForMathlib.Combinatorics.Basic
  let n := Name.mkStr (Name.mkStr (Name.mkStr (Name.mkStr (Name.mkNum base 0) "Set") "IsSidon") "avoids_isAPOfLength_three") "_proof_1_1"
  return mkConst n

#check sidonBug

example : False := by
  have h := sidonBug (A := (Set.univ : Set ℕ)) (Y := (Set.univ : Set ℕ)) 0 0
  exact h (by norm_num)

#print axioms _example
