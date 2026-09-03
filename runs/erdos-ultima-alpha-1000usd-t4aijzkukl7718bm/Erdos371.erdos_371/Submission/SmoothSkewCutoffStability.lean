import Submission.SmoothCutoffSkew
import Submission.WeightedPrimeHarmonic

/-! Uniform continuity of the signed smooth-cutoff correlation under
logarithmically small changes of a cutoff. This gives cancellation for
coalescing cutoffs, not for two distinct fixed power exponents. -/

namespace Erdos371
open Finset Filter
open scoped Topology

namespace FiniteSieve

noncomputable def primeBandLogError : ℝ := 1 + Real.log 4 + primePowerErrorConstant

lemma mediumPrimes_log_sum (B C : ℕ) (hBC : B ≤ C) :
    (∑ p ∈ mediumPrimes B C, Real.log p / (p : ℝ)) =
      primeLogHarmonic C - primeLogHarmonic B := by
  unfold mediumPrimes primeLogHarmonic
  apply sum_sdiff_eq_sub
  intro p hp
  obtain ⟨hpB, hpp⟩ := Nat.mem_primesBelow.mp hp
  exact Nat.mem_primesBelow.mpr ⟨by omega, hpp⟩

/-- The prime reciprocal mass of a band is uniformly controlled by its
relative logarithmic width, with a vanishing lower-cutoff error. -/
lemma mediumPrimes_reciprocal_log_bound (B C : ℕ) (hB : 1 < B) (hBC : B ≤ C) :
    primeReciprocalSum (mediumPrimes B C) ≤
      (Real.log C - Real.log B + primeBandLogError) / Real.log B := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hlogB : 0 < Real.log B := Real.log_pos (by exact_mod_cast hB)
  have hh : Real.log B * primeReciprocalSum (mediumPrimes B C) ≤
      primeLogHarmonic C - primeLogHarmonic B := by
    rw [← mediumPrimes_log_sum B C hBC]
    unfold primeReciprocalSum
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hpB := (mem_mediumPrimes.mp hp).2.1
    have hl : Real.log B ≤ Real.log p :=
      Real.log_le_log hB0 (by exact_mod_cast hpB.le)
    simpa only [mul_one_div] using
      div_le_div_of_nonneg_right hl (Nat.cast_nonneg (α := ℝ) p)
  have hu := primeLogHarmonic_upper C (by omega)
  have hl := primeLogHarmonic_lower B (by omega)
  apply (le_div_iff₀ hlogB).mpr
  unfold primeBandLogError
  nlinarith

/-- This is uniform in both cutoffs: no relation to the averaging endpoint
is needed beyond the hypotheses on their logarithms. -/
theorem mediumPrimes_reciprocal_tendsto_zero (B C : ℕ → ℕ)
    (hB : Tendsto B atTop atTop) (hBC : ∀ᶠ N in atTop, B N ≤ C N)
    (hlog : Tendsto (fun N => Real.log (C N) / Real.log (B N)) atTop (nhds 1)) :
    Tendsto (fun N => primeReciprocalSum (mediumPrimes (B N) (C N))) atTop (nhds 0) := by
  have hb := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hB)
  have he := (tendsto_inv_atTop_zero.comp hb).const_mul primeBandLogError
  have ht := (hlog.sub_const 1).add he
  simp only [sub_self, mul_zero, zero_add] at ht
  apply squeeze_zero' (Eventually.of_forall fun N => primeReciprocalSum_nonneg _) _ ht
  filter_upwards [hB.eventually_gt_atTop 1, hBC] with N hBN hBCN
  have hb0 : Real.log (B N) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hBN : (1 : ℝ) < B N)).ne'
  convert mediumPrimes_reciprocal_log_bound (B N) (C N) hBN hBCN using 1
  rw [add_div, sub_div, div_self hb0]
  simp only [Function.comp_apply]
  ring

end FiniteSieve

lemma smoothIndicator_cutoff_mono (B C n : ℕ) (hBC : B ≤ C) :
    smoothIndicator B n ≤ smoothIndicator C n := by
  by_cases hb : Nat.maxPrimeFac n ≤ B
  · simp [smoothIndicator, hb, hb.trans hBC]
  · simpa only [smoothIndicator, if_neg hb] using (smoothIndicator_bounds C n).1

lemma smoothIndicator_band_le_primeDivCount (B C n : ℕ) (hB : 1 ≤ B) (hBC : B ≤ C)
    (hn : 0 < n) :
    smoothIndicator C n - smoothIndicator B n ≤ primeDivCount (mediumPrimes B C) n := by
  have hnneg : 0 ≤ primeDivCount (mediumPrimes B C) n := by
    unfold primeDivCount
    apply sum_nonneg
    intros
    split_ifs <;> norm_num
  by_cases hbn : Nat.maxPrimeFac n ≤ B
  · have hcn := hbn.trans hBC
    simpa [smoothIndicator, hbn, hcn] using hnneg
  by_cases hcn : Nat.maxPrimeFac n ≤ C
  · have hn1 : 1 < n := by
      by_contra h
      have he : n = 1 := by omega
      simp [he] at hbn
      omega
    have hp : Nat.maxPrimeFac n ∈ mediumPrimes B C :=
      mem_mediumPrimes.mpr ⟨Nat.prime_maxPrimeFac_of_one_lt n hn1, by omega, hcn⟩
    have hh : (if Nat.maxPrimeFac n ∣ n then (1 : ℝ) else 0) ≤
        primeDivCount (mediumPrimes B C) n := by
      unfold primeDivCount
      exact single_le_sum (f := fun p => if p ∣ n then (1 : ℝ) else 0)
        (fun _ _ => by dsimp only; split_ifs <;> norm_num) hp
    simpa [smoothIndicator, hbn, hcn, Nat.maxPrimeFac_dvd] using hh
  · simpa [smoothIndicator, hbn, hcn] using hnneg

lemma smoothIndicator_band_sum_le (B C N : ℕ) (hB : 1 ≤ B) (hBC : B ≤ C) :
    (∑ n ∈ range N, (smoothIndicator C (n+1) - smoothIndicator B (n+1))) ≤
      N * primeReciprocalSum (mediumPrimes B C) := by
  calc
    _ ≤ ∑ n ∈ range N, primeDivCount (mediumPrimes B C) (n+1) :=
      sum_le_sum fun n _ => smoothIndicator_band_le_primeDivCount B C (n+1) hB hBC (by omega)
    _ = ∑ p ∈ mediumPrimes B C, ((N / p : ℕ) : ℝ) := primeDivCount_sum _ _
    _ ≤ _ := by
      unfold primeReciprocalSum
      rw [mul_sum]
      exact sum_le_sum fun p _ => by
        simpa only [mul_one_div] using (Nat.cast_div_le (m := N) (n := p) (α := ℝ))

private lemma smoothSkew_cutoff_change_term (B C D n : ℕ) (hBC : B ≤ C) :
    |(smoothIndicator B (n+1)*smoothIndicator D (n+2) -
        smoothIndicator D (n+1)*smoothIndicator B (n+2)) -
      (smoothIndicator C (n+1)*smoothIndicator D (n+2) -
        smoothIndicator D (n+1)*smoothIndicator C (n+2))| ≤
      (smoothIndicator C (n+1)-smoothIndicator B (n+1)) +
        (smoothIndicator C (n+2)-smoothIndicator B (n+2)) := by
  unfold smoothIndicator
  split_ifs <;> norm_num <;> omega

/-- A uniform finite bound for changing either smoothness threshold. -/
theorem smoothCutoffSkew_change_bound (B C D N : ℕ) (hB : 1 ≤ B) (hBC : B ≤ C) :
    |smoothCutoffSkew B D N - smoothCutoffSkew C D N| ≤
      2 * N * primeReciprocalSum (mediumPrimes B C) + 1 := by
  let f : ℕ → ℝ := fun n => smoothIndicator C (n+1)-smoothIndicator B (n+1)
  have hf0 (n : ℕ) : 0 ≤ f n := sub_nonneg.mpr (smoothIndicator_cutoff_mono B C _ hBC)
  have hf1 (n : ℕ) : f n ≤ 1 := by
    dsimp only [f]
    have h1 := (smoothIndicator_bounds C (n+1)).2
    have h2 := (smoothIndicator_bounds B (n+1)).1
    linarith
  have hshift : (∑ n ∈ range N, f (n+1)) ≤ (∑ n ∈ range N, f n) + 1 := by
    have hh := sum_range_sub f N
    rw [sum_sub_distrib] at hh
    linarith [hf0 0, hf1 N]
  have hsum : (∑ n ∈ range N, f n) ≤ N * primeReciprocalSum (mediumPrimes B C) :=
    smoothIndicator_band_sum_le B C N hB hBC
  unfold smoothCutoffSkew
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ range N, |(smoothIndicator B (n+1)*smoothIndicator D (n+2) -
          smoothIndicator D (n+1)*smoothIndicator B (n+2)) -
        (smoothIndicator C (n+1)*smoothIndicator D (n+2) -
          smoothIndicator D (n+1)*smoothIndicator C (n+2))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ range N, (f n + f (n+1)) :=
      sum_le_sum fun n _ => smoothSkew_cutoff_change_term B C D n hBC
    _ ≤ _ := by
      rw [sum_add_distrib]
      linarith

/-- Stability under a logarithmically vanishing cutoff perturbation, uniformly
in the other cutoff. The two sequences need not be fixed powers of N. -/
theorem smoothCutoffSkew_log_cutoff_stability (B C D : ℕ → ℕ)
    (hB : Tendsto B atTop atTop) (hBC : ∀ᶠ N in atTop, B N ≤ C N)
    (hlog : Tendsto (fun N => Real.log (C N) / Real.log (B N)) atTop (nhds 1)) :
    Tendsto (fun N : ℕ =>
      (smoothCutoffSkew (B N) (D N) N - smoothCutoffSkew (C N) (D N) N) / N)
      atTop (nhds 0) := by
  have ht := ((FiniteSieve.mediumPrimes_reciprocal_tendsto_zero B C hB hBC hlog).const_mul 2).add
    tendsto_one_div_atTop_nhds_zero_nat
  simp only [mul_zero, add_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [hB.eventually_ge_atTop 1, hBC, eventually_gt_atTop (0 : ℕ)] with N hBN hBCN hN
  have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [norm_div, Real.norm_natCast, Real.norm_eq_abs]
  have hh := div_le_div_of_nonneg_right (smoothCutoffSkew_change_bound (B N) (C N) (D N) N hBN hBCN)
    (Nat.cast_nonneg (α := ℝ) N)
  convert hh using 1
  field_simp

/-- In particular, the signed skew cancels when the two cutoffs coalesce
on the logarithmic scale. This does not establish cancellation for distinct
fixed positive exponents. -/
theorem smoothCutoffSkew_coalescing_cancellation (B C : ℕ → ℕ)
    (hB : Tendsto B atTop atTop) (hBC : ∀ᶠ N in atTop, B N ≤ C N)
    (hlog : Tendsto (fun N => Real.log (C N) / Real.log (B N)) atTop (nhds 1)) :
    Tendsto (fun N : ℕ => smoothCutoffSkew (B N) (C N) N / N) atTop (nhds 0) := by
  have hh := smoothCutoffSkew_log_cutoff_stability B C C hB hBC hlog
  simpa only [smoothCutoffSkew, sub_self, sum_const_zero, sub_zero] using hh

/-- Positive limiting logarithmic exponent forces a cutoff to diverge. -/
lemma cutoff_atTop_of_positive_log_exponent (B : ℕ → ℕ) (u : ℝ) (hu : 0 < u)
    (hB : Tendsto (fun N : ℕ => Real.log (B N) / Real.log N) atTop (nhds u)) :
    Tendsto B atTop atTop := by
  have hl := hB.pos_mul_atTop hu (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have ht : Tendsto (fun N => Real.log (B N)) atTop atTop := by
    apply hl.congr'
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    exact div_mul_cancel₀ _ (Real.log_pos (by exact_mod_cast hN : (1 : ℝ) < N)).ne'
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [ht.eventually_gt_atTop (Real.log (k+1 : ℕ))] with N hN
  have hklog : 0 ≤ Real.log (k+1 : ℕ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ k+1 by omega))
  have hb0 : (0 : ℝ) < B N := by
    by_contra h
    have hz : B N = 0 := by exact_mod_cast (le_antisymm (not_lt.mp h) (Nat.cast_nonneg (B N)))
    simp only [hz, Nat.cast_zero, Real.log_zero] at hN
    linarith
  by_contra h
  have hb : (B N : ℝ) ≤ (k+1 : ℕ) := by exact_mod_cast (show B N ≤ k+1 by omega)
  exact hN.not_ge (Real.log_le_log hb0 hb)

/-- Two cutoffs with the same positive limiting power exponent may be
interchanged, uniformly in the other cutoff. -/
theorem smoothCutoffSkew_same_exponent_stability (B C D : ℕ → ℕ) (u : ℝ) (hu : 0 < u)
    (hBC : ∀ᶠ N in atTop, B N ≤ C N)
    (hB : Tendsto (fun N : ℕ => Real.log (B N) / Real.log N) atTop (nhds u))
    (hC : Tendsto (fun N : ℕ => Real.log (C N) / Real.log N) atTop (nhds u)) :
    Tendsto (fun N : ℕ =>
      (smoothCutoffSkew (B N) (D N) N - smoothCutoffSkew (C N) (D N) N) / N)
      atTop (nhds 0) := by
  apply smoothCutoffSkew_log_cutoff_stability B C D
    (cutoff_atTop_of_positive_log_exponent B u hu hB) hBC
  have hh := hC.div hB hu.ne'
  rw [div_self hu.ne'] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  have hn : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN : (1 : ℝ) < N)).ne'
  dsimp only [Pi.div_apply]
  exact div_div_div_cancel_right₀ hn _ _

/-- A fixed multiplicative change is logarithmically negligible, even for
cutoffs growing at an arbitrary rate. -/
theorem smoothCutoffSkew_bounded_multiple_stability (B D : ℕ → ℕ) (K : ℕ) (hK : 0 < K)
    (hB : Tendsto B atTop atTop) :
    Tendsto (fun N : ℕ =>
      (smoothCutoffSkew (B N) (D N) N - smoothCutoffSkew (K * B N) (D N) N) / N)
      atTop (nhds 0) := by
  apply smoothCutoffSkew_log_cutoff_stability B (fun N => K * B N) D hB
    (Eventually.of_forall fun N => by nlinarith)
  have hb := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hB)
  have ht := ((tendsto_inv_atTop_zero.comp hb).const_mul (Real.log K)).add_const 1
  simp only [mul_zero, zero_add] at ht
  apply ht.congr'
  filter_upwards [hB.eventually_gt_atTop 1] with N hBN
  have hk0 : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hb0 : (B N : ℝ) ≠ 0 := by exact_mod_cast (show B N ≠ 0 by omega)
  have hlb : Real.log (B N) ≠ 0 := (Real.log_pos (by exact_mod_cast hBN : (1 : ℝ) < B N)).ne'
  simp only [Function.comp_apply, Nat.cast_mul, Real.log_mul hk0 hb0, add_div, div_self hlb]
  ring

#print axioms FiniteSieve.mediumPrimes_reciprocal_log_bound
#print axioms smoothCutoffSkew_change_bound
#print axioms smoothCutoffSkew_log_cutoff_stability
#print axioms smoothCutoffSkew_coalescing_cancellation
#print axioms smoothCutoffSkew_same_exponent_stability
#print axioms smoothCutoffSkew_bounded_multiple_stability

end Erdos371
