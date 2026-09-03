import FormalConjecturesUtil

/-! Safe upper hinge bounds from a retained lower subdistribution. Missing
mass is charged rather than discarding a positive correction. These are
finite algebraic inequalities, not a numerical sieve certificate. -/
namespace Erdos7LowerLawLoss
open scoped BigOperators
set_option autoImplicit false

lemma hinge_sub_min (z t : ℚ) : max 0 (z-t) = z-min t z := by
  by_cases h : t ≤ z
  · rw [min_eq_left h, max_eq_right (sub_nonneg.mpr h)]
  · have hh : z ≤ t := le_of_not_ge h
    rw [min_eq_right hh, max_eq_left (sub_nonpos.mpr hh), sub_self]

/-- A lower sublaw may safely be used in the bounded subtraction term. -/
theorem hinge_upper {X : Type*} [Fintype X]
    (μ D z : X → ℚ) (t : ℚ) (ht : 0 ≤ t)
    (hz : ∀ x, 0 ≤ z x) (hD : ∀ x, D x ≤ μ x) :
    (∑ x, μ x * max 0 (z x-t)) ≤
      (∑ x, μ x*z x) - ∑ x, D x*min t (z x) := by
  simp only [hinge_sub_min, mul_sub, Finset.sum_sub_distrib]
  apply sub_le_sub_left
  exact Finset.sum_le_sum (fun x _ =>
    mul_le_mul_of_nonneg_right (hD x) (le_min ht (hz x)))

/-- The exact missing-mass correction to the unsafe truncated positive-part
formula, provided the full law has total mass1. -/
theorem missing_mass_identity {X : Type*} [Fintype X]
    (D z : X → ℚ) (t M : ℚ) :
    M - (∑ x, D x*min t (z x)) =
      (M-t+∑ x, D x*max 0 (t-z x)) + t*(1-∑ x, D x) := by
  have he (x : X) : min t (z x) = t-max 0 (t-z x) := by
    rw [hinge_sub_min, min_comm (z x) t]
    ring
  simp_rw [he, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

/-- In the distortion notation, the exact mean supplies the unbounded linear
part; only the bounded minimum is evaluated against the lower sublaw. -/
theorem residual_upper {X : Type*} [Fintype X]
    (μ D K : X → ℚ) (c q : ℚ) (hc : 1 ≤ c) (hq : 0 < q)
    (hK : ∀ x, 0 ≤ K x) (hD : ∀ x, D x ≤ μ x) :
    (∑ x, μ x * max 0 (c/q*K x-(c-1))) ≤
      c/q*(∑ x, μ x*K x) - ∑ x, D x*min (c-1) (c/q*K x) := by
  have h := hinge_upper μ D (fun x => c/q*K x) (c-1) (by linarith)
    (by intro x; exact mul_nonneg (div_nonneg (by linarith) hq.le) (hK x)) hD
  convert h using 1
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

#print axioms hinge_upper
#print axioms missing_mass_identity
#print axioms residual_upper
end Erdos7LowerLawLoss
