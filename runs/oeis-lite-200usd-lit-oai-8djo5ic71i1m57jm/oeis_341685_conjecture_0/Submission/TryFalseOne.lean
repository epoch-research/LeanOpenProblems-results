import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
open scoped ZeroObject
example : False := by
  classical
  apply CategoryTheory.hom_inl_inr_false
  all_goals first | infer_instance | norm_num | omega | simp | contradiction | trivial | aesop
