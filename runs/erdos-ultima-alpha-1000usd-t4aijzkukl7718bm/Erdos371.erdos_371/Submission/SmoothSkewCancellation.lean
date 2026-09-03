import Submission.SmoothCutoffSkew

/-! Unconditional cancellation when one smoothness cutoff is subpower.
The power-sized interior cutoffs needed by PowerSmoothReciprocity are not
covered by this theorem. -/

namespace Erdos371
open Finset Filter

lemma smoothCutoffSkew_abs_bound (B C N : ℕ) :
    |smoothCutoffSkew B C N| ≤
      2*(((range N).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ)+4 := by
  have ht (n : ℕ) : |smoothIndicator B (n+1)*smoothIndicator C (n+2)-
      smoothIndicator C (n+1)*smoothIndicator B (n+2)| ≤
        smoothIndicator B (n+1)+smoothIndicator B (n+2) := by
    unfold smoothIndicator
    split_ifs <;> norm_num
  calc
    _ ≤ ∑ n ∈ range N, |smoothIndicator B (n+1)*smoothIndicator C (n+2)-
        smoothIndicator C (n+1)*smoothIndicator B (n+2)| := abs_sum_le_sum_abs _ _
    _ ≤ (∑ n ∈ range N, smoothIndicator B (n+1))+(∑ n ∈ range N, smoothIndicator B (n+2)) := by
      rw [← sum_add_distrib]
      exact sum_le_sum (fun n hn => ht n)
    _ ≤ 2*(((range (N+2)).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) := by
      have h1 := smooth_shifted_indicator_sum_le B N 1
      have h2 := smooth_shifted_indicator_sum_le B N 2
      have hcard : (((range (N+1)).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) ≤
          (((range (N+2)).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) := by
        exact_mod_cast card_le_card (filter_subset_filter _ (range_mono (show N+1 ≤ N+2 by omega)))
      change (∑ n ∈ range N, smoothIndicator B (n+1)) ≤ _ at h1
      change (∑ n ∈ range N, smoothIndicator B (n+2)) ≤ _ at h2
      linarith
    _ ≤ _ := by linarith [smooth_count_add_two_le B N]

lemma smoothCutoffSkew_tendsto_zero_of_smooth_count (B C : ℕ → ℕ)
    (hB : Tendsto (fun N : ℕ => (((range N).filter fun n => Nat.maxPrimeFac n ≤ B N).card : ℝ)/N)
      atTop (nhds 0)) :
    Tendsto (fun N : ℕ => smoothCutoffSkew (B N) (C N) N/N) atTop (nhds 0) := by
  have ht := (hB.const_mul 2).add (tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ))
  simp only [mul_zero,add_zero] at ht
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) _ ht
  intro N
  rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
  have hb := div_le_div_of_nonneg_right (smoothCutoffSkew_abs_bound (B N) (C N) N)
    (Nat.cast_nonneg (α := ℝ) N)
  simpa only [add_div,mul_div_assoc] using hb

/-- Subpower smoothness in the first variable gives cancellation uniformly
in the other cutoff. Fixed positive powers of N are outside the hypothesis. -/
theorem smoothCutoffSkew_subpower_cancellation (B C : ℕ → ℕ)
    (hB : Tendsto (fun N : ℕ => Real.log (B N+1 : ℝ)/Real.log N) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => smoothCutoffSkew (B N) (C N) N/N) atTop (nhds 0) := by
  exact smoothCutoffSkew_tendsto_zero_of_smooth_count B C (subpower_smooth_count_tendsto_zero B hB)

/-- A genuinely vanishing signed band kernel, but only with a subpower
lower cutoff. This does not cover the interior power-cutoff reciprocity
hypothesis required for the density theorem. -/
theorem subpower_band_kernel_cancellation (B C : ℕ → ℕ)
    (hB : ∀ N, 1 ≤ B N) (hBC : ∀ N, B N ≤ C N)
    (hlog : Tendsto (fun N : ℕ => Real.log (B N+1 : ℝ)/Real.log N) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => divisorSkewKernel (primeBandMoebius (B N) (C N))
      (properRoughMoebius (C N)) N/N) atTop (nhds 0) := by
  exact (smoothCutoffSkew_cancellation_iff B C hB hBC).mp
    (smoothCutoffSkew_subpower_cancellation B C hlog)

#print axioms smoothCutoffSkew_subpower_cancellation
#print axioms subpower_band_kernel_cancellation
end Erdos371
