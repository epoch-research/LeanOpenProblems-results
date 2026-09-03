import Submission.GreedySurvivalTotalDrift

/-!
Actual means on a changing finite set. The exact drift numerator is weighted
by the NEXT cardinality. A separate error estimate, not an identification,
is used to pass from that weighted numerator to a uniform conditional mean.
-/
namespace Erdos773.FiniteMovingMean
open Finset
set_option maxHeartbeats 2500000
noncomputable section
variable {α β : Type*}

def mean (S : Finset α) (f : α → ℝ) : ℝ := (∑ u ∈ S, f u)/S.card

lemma card_mul_mean (S : Finset α) (f : α → ℝ) :
    (S.card:ℝ)*mean S f = ∑ u ∈ S, f u := by
  by_cases hS : S = ∅
  · simp [mean, hS]
  · have hc : (S.card:ℝ) ≠ 0 := by exact_mod_cast card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hS)
    exact mul_div_cancel₀ _ hc

lemma centered_sum (S : Finset α) (f : α → ℝ) :
    (∑ u ∈ S, (f u-mean S f)) = 0 := by
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, card_mul_mean, sub_self]

/-- The next cardinality multiplies the mean increment. This identity is
also valid when the next set is empty, using Lean's zero-denominator mean. -/
lemma increment_numerator (S T : Finset α) (f g : α → ℝ) :
    (T.card:ℝ)*(mean T g-mean S f) =
      (∑ u ∈ T, g u)-(∑ u ∈ S, f u)-mean S f*((T.card:ℝ)-S.card) := by
  have hS := card_mul_mean S f
  have hT := card_mul_mean T g
  nlinarith only [hS, hT]

/-- Exact covariance expansion about the actual two means. -/
lemma covariance_expansion (S : Finset α) (f g : α → ℝ) :
    (∑ u ∈ S, (f u-mean S f)*(g u-mean S g)) =
      (∑ u ∈ S, f u*g u)-(S.card:ℝ)*mean S f*mean S g := by
  have hf := card_mul_mean S f
  have hg := card_mul_mean S g
  simp_rw [sub_mul, mul_sub]
  rw [sum_sub_distrib, sum_sub_distrib, sum_sub_distrib, ← sum_mul,
    ← mul_sum, sum_const, nsmul_eq_mul, ← hf, ← hg]
  ring

/-- Weighted drift on a changing survivor set. The death term is centered
at the CURRENT arithmetic mean, rather than omitted or frozen. -/
theorem weighted_survivor_drift [DecidableEq α] (S : Finset α) (T : α → Finset α)
    (hT : ∀ v ∈ S, T v ⊆ S) (f : α → ℝ) (g : α → α → ℝ) :
    (∑ v ∈ S, (T v).card*(mean (T v) (g v)-mean S f)) =
      (∑ u ∈ S, ∑ v ∈ S.filter (fun v => u ∈ T v), (g v u-f u))-
      (∑ u ∈ S, ((S.card:ℝ)-(S.filter (fun v => u ∈ T v)).card)*(f u-mean S f)) := by
  have hb := GreedySurvivalTotalDrift.survival_balance S T hT
    (fun u => f u-mean S f) (fun v u => g v u-mean S f)
  have he (v : α) :
      (∑ u ∈ T v, (g v u-mean S f))-(∑ u ∈ S, (f u-mean S f)) =
      (T v).card*(mean (T v) (g v)-mean S f) := by
    rw [centered_sum, sub_zero, sum_sub_distrib, sum_const, nsmul_eq_mul,
      mul_sub, card_mul_mean]
  rw [sum_congr rfl (fun v _ => he v)] at hb
  simpa only [sub_sub_sub_cancel_right] using hb

/-- Finite reweighting error before any division. The deficit from the
current cardinality costs the actual total absolute mean variation. -/
theorem reweighting_error (S : Finset β) (z w : β → ℝ) (Q B : ℝ)
    (hB : ∀ v ∈ S, |Q-w v| ≤ B) :
    |Q*(∑ v ∈ S, z v)-(∑ v ∈ S, w v*z v)| ≤ B*(∑ v ∈ S, |z v|) := by
  rw [mul_sum, ← sum_sub_distrib]
  calc
    _ ≤ ∑ v ∈ S, |Q*z v-w v*z v| := abs_sum_le_sum_abs _ _
    _ = ∑ v ∈ S, |Q-w v| * |z v| := by simp only [← sub_mul, abs_mul]
    _ ≤ ∑ v ∈ S, B*|z v| :=
      sum_le_sum (fun v hv => mul_le_mul_of_nonneg_right (hB v hv) (abs_nonneg _))
    _ = _ := (mul_sum _ _ _).symm

/-- A weighted upper drift is an ordinary upper drift only AFTER paying
the reweighting error. No sign of the individual increments is presumed. -/
theorem average_upper_of_weighted (S : Finset β) (z w : β → ℝ) (Q B D V : ℝ)
    (hQ : 0 < Q) (hB0 : 0 ≤ B) (hB : ∀ v ∈ S, |Q-w v| ≤ B)
    (hD : (∑ v ∈ S, w v*z v) ≤ D) (hV : (∑ v ∈ S, |z v|) ≤ V) :
    (∑ v ∈ S, z v)/Q ≤ (D+B*V)/Q^2 := by
  have hh := (abs_le.mp (reweighting_error S z w Q B hB)).2
  have hv := mul_le_mul_of_nonneg_left hV hB0
  have hu : Q*(∑ v ∈ S, z v) ≤ D+B*V := by linarith only [hh, hD, hv]
  calc
    _ = (Q*(∑ v ∈ S, z v))/Q^2 := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hu (sq_nonneg Q)

#print axioms card_mul_mean
#print axioms increment_numerator
#print axioms covariance_expansion
#print axioms weighted_survivor_drift
#print axioms reweighting_error
#print axioms average_upper_of_weighted
end
end Erdos773.FiniteMovingMean
