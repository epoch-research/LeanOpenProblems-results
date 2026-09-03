import FormalConjecturesUtil
import Submission.PrimeDiscrepancy
import Submission.SmoothDensity
import Submission.LogSmoothCount

/-! Common dilation of the two endpoints preserves their largest-prime-factor
comparison outside a controlled smooth exceptional set. The multipliers can
vary with both the endpoint and the counting range. This is not a result about
consecutive comparisons at the dilated inputs, and does not prove Erdős 371. -/

namespace Erdos371CommonDilation

open Finset Filter Erdos371PrimeDiscrepancy Erdos371Exploration
open scoped Topology

def scaledSign (a n : ℕ) : ℤ :=
  if P (a*n) < P (a*(n+1)) then 1 else -1

lemma comparison_common_floor (q x y : ℕ) (h : q ≤ x) :
    (if max q x < max q y then (1 : ℤ) else -1) =
      (if x < y then 1 else -1) := by
  have he : max q x < max q y ↔ x < y := by omega
  simp only [he]

lemma scaledSign_eq {a n : ℕ} (ha : 0 < a) (hn : 0 < n)
    (h : P a ≤ P n) : scaledSign a n = sign n := by
  unfold scaledSign sign P
  rw [Nat.maxPrimeFac_mul ha.ne' hn.ne',
    Nat.maxPrimeFac_mul ha.ne' (by omega : n+1 ≠ 0)]
  exact comparison_common_floor _ _ _ h

/-- No bound on the size of the multiplier is necessary: only its largest
prime factor enters the exceptional set. -/
lemma pointwise_error_bound {a K : ℕ} (ha : 0 < a) (hK : P a ≤ K) (n : ℕ) :
    |(scaledSign a n : ℝ) - (sign n : ℝ)| ≤
      if P n ≤ K then 2 else 0 := by
  by_cases hnK : P n ≤ K
  · rw [if_pos hnK]
    unfold scaledSign sign
    split_ifs <;> norm_num
  · have hn : 0 < n := by
      by_contra h
      have hn0 : n = 0 := by omega
      simp [hn0, P] at hnK
    have hh : P a ≤ P n := by omega
    rw [scaledSign_eq ha hn hh, sub_self, abs_zero, if_neg hnK]

lemma fixed_changes_hasDensity_zero {a : ℕ} (ha : 0 < a) :
    {n | scaledSign a n ≠ sign n}.HasDensity 0 := by
  apply density_zero_of_subset _ (bounded_maxPrimeFac_hasDensity_zero (P a))
  intro n hn
  change P n ≤ P a
  by_contra hh
  have hn0 : 0 < n := by
    by_contra h
    have he : n = 0 := by omega
    simp [he, P] at hh
  exact hn (scaledSign_eq ha hn0 (by omega))

noncomputable def meanError (a : ℕ → ℕ) (N : ℕ) : ℝ :=
  (∑ n ∈ range N, |(scaledSign (a n) n : ℝ) - (sign n : ℝ)|) / N

lemma meanError_nonneg (a : ℕ → ℕ) (N : ℕ) : 0 ≤ meanError a N := by
  unfold meanError
  positivity

lemma meanError_bound {a : ℕ → ℕ} {K N : ℕ}
    (ha : ∀ n < N, 0 < a n) (hK : ∀ n < N, P (a n) ≤ K) :
    meanError a N ≤
      2 * ((((range N).filter fun n => P n ≤ K).card : ℝ) / N) := by
  have hs : (∑ n ∈ range N, |(scaledSign (a n) n : ℝ) - (sign n : ℝ)|) ≤
      2 * (((range N).filter fun n => P n ≤ K).card : ℝ) := by
    calc
      _ ≤ ∑ n ∈ range N, if P n ≤ K then (2 : ℝ) else 0 := by
        apply sum_le_sum
        intro n hn
        exact pointwise_error_bound (ha n (mem_range.mp hn))
          (hK n (mem_range.mp hn)) n
      _ = _ := by rw [← sum_filter]; simp [mul_comm]
  exact (div_le_div_of_nonneg_right hs (Nat.cast_nonneg N)).trans_eq (by ring)

/-- This is uniform even for a multiplier selected separately at every input.
It still compares `a*n` with `a*(n+1)`, whose difference is `a`, not one. -/
theorem subpower_meanError_tendsto_zero (a : ℕ → ℕ → ℕ) (K : ℕ → ℕ)
    (ha : ∀ᶠ N in atTop, ∀ n < N, 0 < a N n)
    (hK : ∀ᶠ N in atTop, ∀ n < N, P (a N n) ≤ K N)
    (hKpos : ∀ᶠ N in atTop, 0 < K N)
    (hlog : Tendsto (fun N : ℕ => Real.log (K N : ℝ) / Real.log (N : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun N => meanError (a N) N) atTop (𝓝 0) := by
  have hu := (Erdos371LogSmoothCount.moving_smooth_count_tendsto_zero
    K hKpos hlog).const_mul 2
  simp only [mul_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun N => meanError_nonneg (a N) N
  · filter_upwards [ha, hK] with N haN hKN
    exact meanError_bound haN hKN

lemma fixed_meanError_tendsto_zero {a : ℕ} (ha : 0 < a) :
    Tendsto (meanError (fun _ => a)) atTop (𝓝 0) := by
  have hu := (bounded_maxPrimeFac_hasDensity_zero (P a)).const_mul 2
  simp only [mul_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · exact fun N => meanError_nonneg _ N
  · intro N
    dsimp only
    rw [bounded_maxPrimeFac_partialDensity]
    exact meanError_bound (fun _ _ => ha) (fun _ _ => le_rfl)

end Erdos371CommonDilation

#print axioms Erdos371CommonDilation.fixed_changes_hasDensity_zero
#print axioms Erdos371CommonDilation.subpower_meanError_tendsto_zero
#print axioms Erdos371CommonDilation.fixed_meanError_tendsto_zero
