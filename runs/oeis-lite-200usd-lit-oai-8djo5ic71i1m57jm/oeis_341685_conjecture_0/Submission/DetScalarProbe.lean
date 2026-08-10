import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

#check LinearMap.det_id
#check LinearMap.det_smul
#check LinearMap.det_zero
#check LinearMap.det_smulRight
#check LinearMap.det_lsmul
#check LinearMap.det_eq_one_of_finrank_eq_zero
#check finrank_eq_zero_of_not_exists_basis
#check finrank_eq_zero_of_not_module_finite

noncomputable abbrev idEnd : (Padic 3) →ₗ[ℚ] (Padic 3) := 1
noncomputable abbrev zeroEnd : (Padic 3) →ₗ[ℚ] (Padic 3) := 0

example : LinearMap.det idEnd = (1 : ℚ) := by simp [idEnd]
example : LinearMap.det ((2 : ℚ) • idEnd) = (2 : ℚ) ^ Module.finrank ℚ (Padic 3) := by
  simp [idEnd]
example : LinearMap.det ((0 : ℚ) • idEnd) = (0 : ℚ) ^ Module.finrank ℚ (Padic 3) := by
  simp [idEnd]
example : LinearMap.det zeroEnd = (0 : ℚ) ^ Module.finrank ℚ (Padic 3) := by simp [zeroEnd]
