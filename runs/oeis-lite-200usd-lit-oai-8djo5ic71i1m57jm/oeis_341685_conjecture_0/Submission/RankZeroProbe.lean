import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#check Module.rank_pos
#check Module.rank_eq_zero_of_not_exists_basis
#check Module.rank_eq_zero_iff
#check rank_eq_zero_iff
#check Module.rank_eq_zero_iff_forall_zero
#check Module.finrank_of_not_finite
#check Cardinal.toNat_apply_of_aleph0_le
example : Module.rank ℚ (Padic 3) = 0 := by
  exact?
example : Module.Finite ℚ (Padic 3) := by
  exact Module.finite_of_rank_eq_zero (R := ℚ) (M := Padic 3) (by exact?)
