import Submission.RoughMobiusHarmonic
import Submission.BalancedKernel

/-! Exact rank-two reciprocal-discrepancy kernels for asymmetric correlations
of two smooth-number indicators. The formulas do not assert cancellation of
the kernels for growing cutoffs. -/

namespace Erdos371
open Finset

noncomputable def smoothIndicator (B n : ℕ) : ℝ :=
  if Nat.maxPrimeFac n ≤ B then 1 else 0

noncomputable def smoothCutoffSkew (B C N : ℕ) : ℝ :=
  ∑ n ∈ range N, (smoothIndicator B (n+1)*smoothIndicator C (n+2)-
    smoothIndicator C (n+1)*smoothIndicator B (n+2))

noncomputable def divisorConvolution (f : ℕ → ℝ) (n : ℕ) : ℝ := ∑ d ∈ n.divisors, f d

noncomputable def divisorSkewKernel (f g : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ a ∈ range (N+2), ∑ b ∈ range (N+2),
    f a*g b*((bilinearCount N a b : ℝ)-bilinearCount N b a)

lemma divisorConvolution_product_prefix (f g : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ range N, divisorConvolution f (n+1)*divisorConvolution g (n+2)) =
      ∑ a ∈ range (N+2), ∑ b ∈ range (N+2), f a*g b*(bilinearCount N a b : ℝ) := by
  have he (n : ℕ) (hn : n < N) : divisorConvolution f (n+1)*divisorConvolution g (n+2) =
      ∑ a ∈ range (N+2), ∑ b ∈ range (N+2), if a ∣ n+1 ∧ b ∣ n+2 then f a*g b else 0 := by
    unfold divisorConvolution
    rw [sum_divisors_eq_range (n+1) (N+2) (by omega) (by omega),
      sum_divisors_eq_range (n+2) (N+2) (by omega) (by omega),sum_mul]
    apply sum_congr rfl
    intro a ha
    rw [mul_sum]
    apply sum_congr rfl
    intro b hb
    by_cases h1 : a ∣ n+1 <;> by_cases h2 : b ∣ n+2 <;> simp [h1,h2]
  calc
    _ = ∑ n ∈ range N, ∑ a ∈ range (N+2), ∑ b ∈ range (N+2),
        if a ∣ n+1 ∧ b ∣ n+2 then f a*g b else 0 := sum_congr rfl (fun n hn => he n (mem_range.mp hn))
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a ha
      rw [sum_comm]
      apply sum_congr rfl
      intro b hb
      rw [← sum_filter]
      simp [bilinearCount,mul_comm]

lemma divisorConvolution_skew_prefix (f g : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ range N, (divisorConvolution f (n+1)*divisorConvolution g (n+2)-
      divisorConvolution g (n+1)*divisorConvolution f (n+2))) = divisorSkewKernel f g N := by
  rw [sum_sub_distrib,divisorConvolution_product_prefix,divisorConvolution_product_prefix]
  have hs : (∑ a ∈ range (N+2), ∑ b ∈ range (N+2), g a*f b*(bilinearCount N a b : ℝ)) =
      ∑ a ∈ range (N+2), ∑ b ∈ range (N+2), f a*g b*(bilinearCount N b a : ℝ) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    ring
  rw [hs]
  simp only [divisorSkewKernel,mul_sub,sum_sub_distrib]

lemma smoothIndicator_convolution (B n : ℕ) (hB : 1 ≤ B) (hn : 0 < n) :
    divisorConvolution (roughMoebius B) n = smoothIndicator B n :=
  roughMoebius_divisor_sum B n hB hn

lemma smoothCutoffSkew_full_kernel (B C N : ℕ) (hB : 1 ≤ B) (hC : 1 ≤ C) :
    smoothCutoffSkew B C N = divisorSkewKernel (roughMoebius B) (roughMoebius C) N := by
  rw [← divisorConvolution_skew_prefix]
  unfold smoothCutoffSkew
  apply sum_congr rfl
  intro n hn
  rw [smoothIndicator_convolution B (n+1) hB (by omega),smoothIndicator_convolution C (n+2) hC (by omega),
    smoothIndicator_convolution C (n+1) hC (by omega),smoothIndicator_convolution B (n+2) hB (by omega)]

noncomputable def primeBandMoebius (B C d : ℕ) : ℝ :=
  if 1 < d ∧ B < d.minFac ∧ d.minFac ≤ C then (ArithmeticFunction.moebius d : ℝ) else 0

noncomputable def properRoughMoebius (C d : ℕ) : ℝ :=
  if 1 < d ∧ C < d.minFac then (ArithmeticFunction.moebius d : ℝ) else 0

lemma primeBandMoebius_eq_sub (B C d : ℕ) (hBC : B ≤ C) :
    primeBandMoebius B C d = roughMoebius B d-roughMoebius C d := by
  unfold primeBandMoebius roughMoebius
  by_cases hd : d = 1
  · simp [hd]
  · by_cases hd1 : 1 < d
    · by_cases hB : B < d.minFac
      · by_cases hC : C < d.minFac
        · simp [hd,hd1,hB,hC,not_le.mpr hC]
        · simp [hd,hd1,hB,hC,le_of_not_gt hC]
      · have hC : ¬ C < d.minFac := by omega
        simp [hd,hd1,hB,hC]
    · simp [hd,hd1]

lemma properRoughMoebius_eq_sub (C d : ℕ) :
    properRoughMoebius C d = roughMoebius C d-(if d = 1 then 1 else 0) := by
  unfold properRoughMoebius roughMoebius
  by_cases hd : d = 1 <;> simp [hd]

lemma primeBandMoebius_convolution (B C n : ℕ) (hB : 1 ≤ B) (hBC : B ≤ C) (hn : 0 < n) :
    divisorConvolution (primeBandMoebius B C) n = smoothIndicator B n-smoothIndicator C n := by
  unfold divisorConvolution
  simp_rw [primeBandMoebius_eq_sub B C _ hBC,sum_sub_distrib]
  rw [roughMoebius_divisor_sum B n hB hn,roughMoebius_divisor_sum C n (hB.trans hBC) hn]
  rfl

lemma properRoughMoebius_convolution (C n : ℕ) (hC : 1 ≤ C) (hn : 0 < n) :
    divisorConvolution (properRoughMoebius C) n = smoothIndicator C n-1 := by
  unfold divisorConvolution
  simp_rw [properRoughMoebius_eq_sub,sum_sub_distrib]
  rw [roughMoebius_divisor_sum C n hC hn]
  have h1 : 1 ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd _,hn.ne'⟩
  simp [h1,smoothIndicator]

/-- Only a least-prime-factor band in one variable and a proper rough
variable remain. The singleton-divisor terms telescope to an endpoint. -/
theorem smoothCutoffSkew_band_kernel (B C N : ℕ) (hB : 1 ≤ B) (hBC : B ≤ C) :
    smoothCutoffSkew B C N = smoothIndicator C (N+1)-smoothIndicator B (N+1)+
      divisorSkewKernel (primeBandMoebius B C) (properRoughMoebius C) N := by
  have hk := divisorConvolution_skew_prefix (primeBandMoebius B C) (properRoughMoebius C) N
  have he (n : ℕ) :
      smoothIndicator B (n+1)*smoothIndicator C (n+2)-smoothIndicator C (n+1)*smoothIndicator B (n+2) =
      (divisorConvolution (primeBandMoebius B C) (n+1)*divisorConvolution (properRoughMoebius C) (n+2)-
        divisorConvolution (properRoughMoebius C) (n+1)*divisorConvolution (primeBandMoebius B C) (n+2)) +
      ((smoothIndicator B (n+1)-smoothIndicator C (n+1))-(smoothIndicator B (n+2)-smoothIndicator C (n+2))) := by
    rw [primeBandMoebius_convolution B C (n+1) hB hBC (by omega),
      primeBandMoebius_convolution B C (n+2) hB hBC (by omega),
      properRoughMoebius_convolution C (n+1) (hB.trans hBC) (by omega),
      properRoughMoebius_convolution C (n+2) (hB.trans hBC) (by omega)]
    ring
  unfold smoothCutoffSkew
  simp_rw [he,sum_add_distrib]
  rw [hk]
  have ht := sum_range_sub' (fun n => smoothIndicator B (n+1)-smoothIndicator C (n+1)) N
  have hz : smoothIndicator B 1-smoothIndicator C 1 = 0 := by
    simp [smoothIndicator,hB,hB.trans hBC]
  rw [hz] at ht
  rw [ht]
  ring

lemma smoothIndicator_bounds (B n : ℕ) : 0 ≤ smoothIndicator B n ∧ smoothIndicator B n ≤ 1 := by
  unfold smoothIndicator
  split_ifs <;> norm_num

open Filter in
/-- For arbitrary growing cutoffs, endpoint terms are uniformly negligible.
The remaining band-kernel cancellation is not established here. -/
theorem smoothCutoffSkew_cancellation_iff (B C : ℕ → ℕ)
    (hB : ∀ N, 1 ≤ B N) (hBC : ∀ N, B N ≤ C N) :
    Tendsto (fun N : ℕ => smoothCutoffSkew (B N) (C N) N/N) atTop (nhds 0) ↔
      Tendsto (fun N : ℕ => divisorSkewKernel (primeBandMoebius (B N) (C N))
        (properRoughMoebius (C N)) N/N) atTop (nhds 0) := by
  have ht : Tendsto (fun N : ℕ => (smoothIndicator (C N) (N+1)-smoothIndicator (B N) (N+1))/N)
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) _ (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    intro N
    rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    have h1 := smoothIndicator_bounds (B N) (N+1)
    have h2 := smoothIndicator_bounds (C N) (N+1)
    rw [abs_le]
    constructor <;> linarith
  have he (N : ℕ) : smoothCutoffSkew (B N) (C N) N/N =
      (smoothIndicator (C N) (N+1)-smoothIndicator (B N) (N+1))/N+
      divisorSkewKernel (primeBandMoebius (B N) (C N)) (properRoughMoebius (C N)) N/N := by
    rw [smoothCutoffSkew_band_kernel _ _ _ (hB N) (hBC N),add_div]
  constructor
  · intro h
    have hh := h.sub ht
    simp only [sub_zero] at hh
    apply hh.congr' (Eventually.of_forall fun N => ?_)
    dsimp only
    rw [he]
    ring
  · intro h
    have hh := ht.add h
    simp only [add_zero] at hh
    exact hh.congr' (Eventually.of_forall fun N => (he N).symm)

#print axioms smoothCutoffSkew_band_kernel
#print axioms smoothCutoffSkew_cancellation_iff
end Erdos371
