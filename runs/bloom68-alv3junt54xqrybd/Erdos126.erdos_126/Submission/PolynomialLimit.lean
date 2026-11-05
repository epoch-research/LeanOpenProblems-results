import Submission.Limits

/-!
# Polynomial cardinality bounds imply the logarithmic limit

This file is conditional: a uniform quadratic cardinality bound is its only
number-theoretic hypothesis. Arbitrary natural coefficients are allowed, so in
particular a bound `A.card ≤ 12 * supportCount A ^ 2 + 2` can be supplied directly.
The additive constant may be two; no bound with additive constant one is assumed.

The analytic estimate is elementary. Bound the quadratic by a constant times
`(supportCount A + 1) ^ 2`, and apply `log x ≤ x` to
`(ε / 2) * (supportCount A + 1)`. The resulting explicit constant is uniform in
`A`. The reductions from `Submission.Limits` then give the required divergence.
-/

open Filter

namespace Erdos126Aux

/-- An explicit subexponential estimate from a uniform quadratic cardinality bound.
The coefficients may be zero, and the support count may be zero. -/
theorem log_card_le_of_quadratic_cardinality_bound {C0 D0 : ℕ}
    (h : ∀ A : Finset ℕ, A.card ≤ C0 * supportCount A ^ 2 + D0)
    {ε : ℝ} (hε : 0 < ε) (A : Finset ℕ) (hA : 2 ≤ A.card) :
    Real.log (A.card : ℝ) ≤
      (Real.log ((C0 + D0 + 1 : ℕ) : ℝ) + ε - 2 * Real.log (ε / 2)) +
        ε * (supportCount A : ℝ) := by
  have hsq : supportCount A ^ 2 ≤ (supportCount A + 1) ^ 2 :=
    Nat.pow_le_pow_left (Nat.le_add_right _ _) _
  have hone : 1 ≤ (supportCount A + 1) ^ 2 :=
    Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hpoly : C0 * supportCount A ^ 2 + D0 ≤
      (C0 + D0 + 1) * (supportCount A + 1) ^ 2 := by
    calc
      C0 * supportCount A ^ 2 + D0 ≤
          C0 * (supportCount A + 1) ^ 2 + D0 * (supportCount A + 1) ^ 2 := by
        exact add_le_add (Nat.mul_le_mul_left C0 hsq)
          (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left D0 hone)
      _ = (C0 + D0) * (supportCount A + 1) ^ 2 := by ring
      _ ≤ (C0 + D0 + 1) * (supportCount A + 1) ^ 2 := by
        exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have hcard : (A.card : ℝ) ≤
      ((C0 + D0 + 1 : ℕ) : ℝ) * ((supportCount A : ℝ) + 1) ^ 2 := by
    exact_mod_cast (h A).trans hpoly
  have hcardpos : (0 : ℝ) < A.card := by
    exact_mod_cast (show 0 < A.card by omega)
  have hcoeff : (0 : ℝ) < ((C0 + D0 + 1 : ℕ) : ℝ) := by positivity
  have hspos : 0 < (supportCount A : ℝ) + 1 := by positivity
  have hhalf : 0 < ε / 2 := by positivity
  have hlog := Real.log_le_log hcardpos hcard
  rw [Real.log_mul (ne_of_gt hcoeff) (by positivity), Real.log_pow] at hlog
  have hscaled := Real.log_le_self (mul_nonneg hhalf.le hspos.le)
  rw [Real.log_mul (ne_of_gt hhalf) (ne_of_gt hspos)] at hscaled
  norm_num only [Nat.cast_ofNat] at hlog
  nlinarith

/-- Every uniform quadratic cardinality bound gives the uniform subexponential
inequality used in `Submission.Limits`. -/
theorem subexponential_bound_of_quadratic_cardinality_bound {C0 D0 : ℕ}
    (h : ∀ A : Finset ℕ, A.card ≤ C0 * supportCount A ^ 2 + D0) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ A : Finset ℕ, 2 ≤ A.card →
      Real.log (A.card : ℝ) ≤ C + ε * (supportCount A : ℝ) := by
  intro ε hε
  refine ⟨Real.log ((C0 + D0 + 1 : ℕ) : ℝ) + ε - 2 * Real.log (ε / 2), ?_⟩
  exact fun A hA => log_card_le_of_quadratic_cardinality_bound h hε A hA

/-- A uniform quadratic cardinality bound implies divergence of the extremal
support count divided by the logarithm of the cardinality. -/
theorem tendsto_extremal_div_log_of_quadratic_cardinality_bound {C0 D0 : ℕ}
    (h : ∀ A : Finset ℕ, A.card ≤ C0 * supportCount A ^ 2 + D0) :
    Tendsto (fun n : ℕ => (extremal n : ℝ) / Real.log (n : ℝ)) atTop atTop :=
  tendsto_extremal_div_log_of_subexponential_bound
    (subexponential_bound_of_quadratic_cardinality_bound h)

/-- The same implication for any function satisfying the greatest-bound predicate.
In particular, the parent proof can pass a bound with `C0 = 12`, `D0 = 2`. -/
theorem tendsto_div_log_of_quadratic_cardinality_bound_of_isGreatest
    {C0 D0 : ℕ} {f : ℕ → ℕ}
    (hf : ∀ n,
      IsGreatest {m : ℕ | ∀ A : Finset ℕ, A.card = n → m ≤ supportCount A} (f n))
    (h : ∀ A : Finset ℕ, A.card ≤ C0 * supportCount A ^ 2 + D0) :
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log (n : ℝ)) atTop atTop :=
  tendsto_div_log_of_subexponential_bound_of_isGreatest hf
    (subexponential_bound_of_quadratic_cardinality_bound h)

end Erdos126Aux
