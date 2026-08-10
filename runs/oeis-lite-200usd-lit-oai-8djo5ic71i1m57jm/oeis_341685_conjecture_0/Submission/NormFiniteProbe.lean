import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra Module

#check Algebra.norm
#check Algebra.norm_eq_one_of_not_module_finite
#check Algebra.norm_zero
#check Algebra.norm_one

example : Algebra.norm ℚ (0 : Padic 3) = (0 : ℚ) := by
  simp

example : Module.Finite ℚ (Padic 3) := by
  by_contra h
  have h1 : Algebra.norm ℚ (0 : Padic 3) = (1 : ℚ) := Algebra.norm_eq_one_of_not_module_finite h 0
  have h0 : Algebra.norm ℚ (0 : Padic 3) = (0 : ℚ) := by simp
  omega

example : IsAlgebraic ℚ xi_3 := by
  haveI : Module.Finite ℚ (Padic 3) := by
    by_contra h
    have h1 : Algebra.norm ℚ (0 : Padic 3) = (1 : ℚ) := Algebra.norm_eq_one_of_not_module_finite h 0
    have h0 : Algebra.norm ℚ (0 : Padic 3) = (0 : ℚ) := by simp
    norm_num [h0] at h1
  exact IsAlgebraic.of_finite ℚ xi_3
