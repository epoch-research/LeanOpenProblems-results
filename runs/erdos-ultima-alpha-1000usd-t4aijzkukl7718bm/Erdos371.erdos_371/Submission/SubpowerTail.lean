import Submission.SubpowerSmooth

/-! The rough mixed-tail reduction is valid for every subpower prime cutoff.
The resulting mixed-tail limit is not proved here. -/

namespace Erdos371

open Filter in
lemma lowLeastDivisorGroup_average_zero_of_smooth_count (B : ℕ → ℕ)
    (hB : Tendsto (fun N : ℕ =>
      (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B N).card : ℝ) / N)
      atTop (nhds 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, lowLeastDivisorGroup (B N) n) / N)
      atTop (nhds 0) := by
  apply squeeze_zero_norm (a := fun N : ℕ =>
    (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B N).card : ℝ) / N) _ hB
  intro N
  rw [norm_div, Real.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖lowLeastDivisorGroup (B N) n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, (if Nat.maxPrimeFac n ≤ B N then (1 : ℝ) else 0) :=
      Finset.sum_le_sum fun n _ => lowLeastDivisorGroup_norm_le_indicator (B N) n
    _ = _ := by simp

open Filter in
lemma lowLeastDivisorGroup_shifted_average_zero_of_smooth_count (B : ℕ → ℕ)
    (hB : Tendsto (fun N : ℕ =>
      (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B N).card : ℝ) / N)
      atTop (nhds 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
      lowLeastDivisorGroup (B N) (n + 1)) / N) atTop (nhds 0) := by
  have he (B N : ℕ) :
      (∑ n ∈ Finset.range N, lowLeastDivisorGroup B (n + 1)) =
        (∑ n ∈ Finset.range N, lowLeastDivisorGroup B n) + lowLeastDivisorGroup B N := by
    have h := Finset.sum_range_succ' (lowLeastDivisorGroup B) N
    rw [Finset.sum_range_succ] at h
    simpa only [lowLeastDivisorGroup_zero, add_zero] using h.symm
  have ht : Tendsto (fun N : ℕ => lowLeastDivisorGroup (B N) N / N) atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun N : ℕ => (1 : ℝ) / N) _ tendsto_one_div_atTop_nhds_zero_nat
    intro N
    rw [norm_div, Real.norm_natCast]
    exact div_le_div_of_nonneg_right (lowLeastDivisorGroup_norm_le_one _ N) (Nat.cast_nonneg N)
  have h := (lowLeastDivisorGroup_average_zero_of_smooth_count B hB).add ht
  simpa only [he, add_div, zero_add] using h

open Filter in
lemma density_iff_rough_large_tail_of_smooth_count (B : ℕ → ℕ)
    (hB : Tendsto (fun N : ℕ =>
      (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B N).card : ℝ) / N)
      atTop (nhds 0)) :
    {n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
        roughLargeDivisorTail (B N) (nearLinearCutoff N) (n + 1)) / N)
        atTop (nhds 0) := by
  rw [density_iff_shifted_sign_average]
  have herr := (roughSmallDivisorSum_nearLinear_tendsto B).add
    (lowLeastDivisorGroup_shifted_average_zero_of_smooth_count B hB)
  simp only [add_zero] at herr
  have he (N : ℕ) :
      (∑ n ∈ Finset.range N, roughSmallDivisorSum (B N) (nearLinearCutoff N) (n + 1)) / N +
      (∑ n ∈ Finset.range N, lowLeastDivisorGroup (B N) (n + 1)) / N +
      (∑ n ∈ Finset.range N, roughLargeDivisorTail (B N) (nearLinearCutoff N) (n + 1)) / N =
        -((∑ n ∈ Finset.range N, factorSign (n + 1)) / N) := by
    rw [← add_div, ← add_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have ht (n : ℕ) :
        roughSmallDivisorSum (B N) (nearLinearCutoff N) (n + 1) +
        lowLeastDivisorGroup (B N) (n + 1) +
        roughLargeDivisorTail (B N) (nearLinearCutoff N) (n + 1) = -factorSign (n + 1) := by
      linarith [rough_small_add_tail_add_low (B N) (nearLinearCutoff N) (n + 1) (by omega)]
    simp_rw [ht, Finset.sum_neg_distrib, neg_div]
  constructor
  · intro h
    have ht := h.neg.sub herr
    simp only [neg_zero, sub_zero] at ht
    apply ht.congr
    intro N
    linarith [he N]
  · intro h
    have ht := (herr.add h).neg
    simp only [add_zero, neg_zero] at ht
    apply ht.congr
    intro N
    linarith [he N]

open Filter in
lemma density_iff_rough_mixed_tail_of_smooth_count (B : ℕ → ℕ)
    (hB : Tendsto (fun N : ℕ =>
      (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B N).card : ℝ) / N)
      atTop (nhds 0)) :
    {n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
        roughMixedDivisorTail (B N) (nearLinearCutoff N) (n + 1)) / N)
        atTop (nhds 0) := by
  rw [density_iff_rough_large_tail_of_smooth_count B hB]
  have he := rough_one_sided_average_tendsto_zero B nearLinearCutoff
  constructor
  · intro h
    have ht := h.sub he
    simp only [sub_zero] at ht
    apply ht.congr
    intro N
    ring
  · intro h
    simpa only [sub_add_cancel, add_zero] using he.add h

open Filter in
/-- The remaining limit is an equivalent unproved cancellation problem,
now allowing any subpower least-prime-factor cutoff. -/
theorem density_iff_subpower_rough_mixed_tail (B : ℕ → ℕ)
    (hB : Tendsto (fun N => Real.log (B N + 1 : ℝ) / Real.log N) atTop (nhds 0)) :
    {n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
        roughMixedDivisorTail (B N) (nearLinearCutoff N) (n + 1)) / N)
        atTop (nhds 0) :=
  density_iff_rough_mixed_tail_of_smooth_count B (subpower_smooth_count_tendsto_zero B hB)

open Filter in
theorem density_iff_subpowerCutoff_mixed_tail :
    {n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
        roughMixedDivisorTail (subpowerCutoff N) (nearLinearCutoff N) (n + 1)) / N)
        atTop (nhds 0) :=
  density_iff_subpower_rough_mixed_tail subpowerCutoff subpowerCutoff_log_ratio_tendsto_zero

#print axioms density_iff_subpower_rough_mixed_tail
#print axioms density_iff_subpowerCutoff_mixed_tail
end Erdos371
