import Submission.Reduction
import Submission.Attenuation

/-!
# Exact Ramsey specialization of the conditional attenuation criterion

No recurrence for Ramsey numbers is asserted here. Each disproof criterion has
an explicit, unproved-in-this-development combinatorial attenuation hypothesis.
This file does not import or use either theorem in `Submission.Spec`.
-/

set_option autoImplicit false

namespace RamseyAttenuation

open Combinatorics Real Filter RealRecords
open scoped Topology

noncomputable def ramseyLog (n : ℕ) : ℝ := Real.logb 2 (hypergraphRamsey 3 n : ℝ)

/-- The exact tower comparison, including the possible zero value of the
natural-valued function on the right. -/
theorem tower_le_iff_log (n : ℕ) :
    (2 : ℕ) ^ (2 ^ n) ≤ hypergraphRamsey 3 n ↔
      (2 : ℝ) ^ n ≤ ramseyLog n := by
  have htpos : 0 < (2 : ℝ) ^ ((2 : ℝ) ^ n) := by positivity
  have htlog : Real.logb 2 ((2 : ℝ) ^ ((2 : ℝ) ^ n)) = (2 : ℝ) ^ n :=
    Real.logb_rpow (by norm_num) (by norm_num)
  constructor
  · intro h
    have hr : (2 : ℝ) ^ ((2 : ℝ) ^ n) ≤ (hypergraphRamsey 3 n : ℝ) := by
      rw [tower_cast]
      exact_mod_cast h
    simpa only [htlog, ramseyLog] using
      Real.logb_le_logb_of_le (by norm_num : 1 < (2 : ℝ)) htpos hr
  · intro h
    have hp : 0 < hypergraphRamsey 3 n := by
      by_contra! hn
      have hz : hypergraphRamsey 3 n = 0 := Nat.eq_zero_of_le_zero hn
      have hpow : 0 < (2 : ℝ) ^ n := by positivity
      simp only [ramseyLog, hz, Nat.cast_zero, Real.logb_zero] at h
      linarith
    have hr : (2 : ℝ) ^ ((2 : ℝ) ^ n) ≤ (hypergraphRamsey 3 n : ℝ) := by
      apply (Real.logb_le_logb (by norm_num : 1 < (2 : ℝ)) htpos
        (by exact_mod_cast hp)).mp
      simpa only [htlog, ramseyLog] using h
    rw [tower_cast] at hr
    exact_mod_cast hr

/-- Exact logarithmic form of the supplied conjecture. -/
theorem exact_logarithmic_reduction :
    (∃ c > 0, ∀ᶠ n in atTop,
      (2 : ℝ) ^ (2 : ℝ) ^ (c * n) ≤ hypergraphRamsey 3 n) ↔
      ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ n ≤ ramseyLog n := by
  rw [exact_reduction]
  exact Filter.eventually_congr (Filter.Eventually.of_forall tower_le_iff_log)

/-- Conditional criterion only: the substantive Ramsey inequality is `hatt`.
The error condition permits every fixed polynomial error. -/
theorem disproof_of_record_attenuation
    {e : ℕ → ℝ} {j : ℕ} {a : ℝ} (ha : 0 < a)
    (he : Tendsto (fun n : ℕ => (n : ℝ) * e n / (2 : ℝ) ^ n) atTop (𝓝 0))
    (hatt : ∀ᶠ n in atTop, IsLogarithmicRecord ramseyLog n →
      ramseyLog n ≤ (2 : ℝ) ^ j * (1 - a / (n : ℝ)) * ramseyLog (n - j) + e n) :
    ¬ (∃ c > 0, ∀ᶠ n in atTop,
      (2 : ℝ) ^ (2 : ℝ) ^ (c * n) ≤ hypergraphRamsey 3 n) := by
  intro h
  exact not_eventually_exp_lower_of_record_attenuation ha he hatt
    (exact_logarithmic_reduction.mp h)

/-- Polynomial-error specialization, still conditional on the actual
Ramsey attenuation inequality at every sufficiently late record. -/
theorem disproof_of_record_attenuation_polynomial
    {j : ℕ} {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ)
    (hatt : ∀ᶠ n in atTop, IsLogarithmicRecord ramseyLog n →
      ramseyLog n ≤ (2 : ℝ) ^ j * (1 - a / (n : ℝ)) * ramseyLog (n - j) +
        p.eval (n : ℝ)) :
    ¬ (∃ c > 0, ∀ᶠ n in atTop,
      (2 : ℝ) ^ (2 : ℝ) ^ (c * n) ≤ hypergraphRamsey 3 n) := by
  exact disproof_of_record_attenuation ha (tendsto_scaled_polynomial_error p) hatt

/-- The same conditional result in the exact cofinal natural-number form. -/
theorem cofinal_strict_upper_of_record_attenuation_polynomial
    {j : ℕ} {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ)
    (hatt : ∀ᶠ n in atTop, IsLogarithmicRecord ramseyLog n →
      ramseyLog n ≤ (2 : ℝ) ^ j * (1 - a / (n : ℝ)) * ramseyLog (n - j) +
        p.eval (n : ℝ)) :
    ∀ N : ℕ, ∃ n ≥ N, hypergraphRamsey 3 n < (2 : ℕ) ^ (2 ^ n) := by
  exact exact_negation.mp (disproof_of_record_attenuation_polynomial ha p hatt)

end RamseyAttenuation

#print axioms RamseyAttenuation.tower_le_iff_log
#print axioms RamseyAttenuation.exact_logarithmic_reduction
#print axioms RamseyAttenuation.disproof_of_record_attenuation
#print axioms RamseyAttenuation.disproof_of_record_attenuation_polynomial
#print axioms RamseyAttenuation.cofinal_strict_upper_of_record_attenuation_polynomial
