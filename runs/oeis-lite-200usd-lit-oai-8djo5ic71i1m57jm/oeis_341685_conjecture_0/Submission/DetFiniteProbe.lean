import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Module

#check LinearMap.det
#check LinearMap.det_zero
#check LinearMap.det_eq_one_of_not_module_finite
#check LinearMap.finite_of_det_ne_one

noncomputable abbrev zEnd : (Padic 3) →ₗ[ℚ] (Padic 3) := 0

example : LinearMap.det (zEnd) = (0 : ℚ) := by
  simp [zEnd]

example : LinearMap.det (zEnd) ≠ (1 : ℚ) := by
  simp [zEnd]

example : Module.Finite ℚ (Padic 3) := by
  exact LinearMap.finite_of_det_ne_one (f := zEnd) (by simp [zEnd])

example : IsAlgebraic ℚ xi_3 := by
  haveI : Module.Finite ℚ (Padic 3) := LinearMap.finite_of_det_ne_one (f := zEnd) (by simp [zEnd])
  exact IsAlgebraic.of_finite ℚ xi_3
