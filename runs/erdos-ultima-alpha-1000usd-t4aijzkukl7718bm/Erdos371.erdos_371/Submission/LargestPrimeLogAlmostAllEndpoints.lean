import Submission.StableHarmonicPrefixAbsoluteZero
import Submission.HarmonicLargestPrimeHalf

/-! Ordinary largest-prime rise proportions converge to one half at
logarithmically almost all endpoints. This does NOT prove convergence at
every endpoint, so it is not a solution of the conjecture in Spec.lean. -/
namespace Erdos371.FiniteInformation
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma harmonicPrefixBias_perturbation_bound (N : ℕ) (f g : ℕ → ℝ) :
    harmonicPrefixBias N f ≤ harmonicPrefixBias N g+
      harmonicRangeMean (N+1) (fun n => |f n-g n|) := by
  have hp (M : ℕ) : |prefixMean M f| ≤ |prefixMean M g|+prefixMean M (fun n => |f n-g n|) := by
    have ht := abs_sub_le (prefixMean M f) (prefixMean M g) 0
    simp only [sub_zero] at ht
    have he : |prefixMean M f-prefixMean M g| ≤ prefixMean M (fun n => |f n-g n|) := by
      rw [← prefixMean_sub]
      unfold prefixMean
      rw [abs_div,abs_of_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
      exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg M)
    linarith
  have hm := mean_mono (harmonicPrefixLaw N) _ _ (fun i => hp (harmonicPrefixLength N i))
  simpa only [mean_add,harmonicPrefixLaw_representation,harmonicPrefixBias,harmonicRangeMean] using hm

lemma harmonicMean_abs_prefix_zero_of_bias_zero (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (h : Tendsto (fun N => harmonicPrefixBias N f) atTop (𝓝 0)) :
    Tendsto (fun N => harmonicMean (N+1) (fun n => |prefixMean n f|)) atTop (𝓝 0) := by
  let G := fun n => |prefixMean n f|
  have hG (n : ℕ) : |G n| ≤ 1 := by simpa only [G,abs_abs] using prefixMean_unit_bound f hf n
  have he : Tendsto (fun N => harmonicPrefixBias N f-harmonicMean (N+1) G) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ (tendsto_const_nhds.div_atTop harmonic_real_tendsto :
      Tendsto (fun N => (4 : ℝ)/(harmonic (N+1) : ℝ)) atTop (𝓝 0))
    intro N
    rw [Real.norm_eq_abs]
    have h₁ := mean_harmonicPrefixLaw_range_error N G hG
    have h₂ := harmonicMean_range_error N G hG
    have ht := abs_sub_le (harmonicPrefixBias N f) (harmonicRangeMean (N+1) G) (harmonicMean (N+1) G)
    change |harmonicPrefixBias N f-harmonicRangeMean (N+1) G| ≤ _ at h₁
    calc
      _ ≤ _ := ht
      _ ≤ 2/(harmonic (N+1) : ℝ)+2/(harmonic (N+1) : ℝ) := add_le_add h₁ h₂
      _ = _ := by ring
  simpa only [sub_sub_cancel,sub_zero] using h.sub he
end Erdos371.FiniteInformation

namespace Erdos371
open Finset Filter FiniteInformation DilationSpectrum
open scoped Topology
set_option autoImplicit false

lemma localFactorSign_harmonic_prefix_abs_zero (Q : ℕ) :
    Tendsto (fun N => harmonicPrefixBias N (localFactorSign Q)) atTop (𝓝 0) :=
  stable_finite_labels_harmonic_prefix_abs_zero (localPrimeLabel Q)
    (localPrimeLabel_mean_dilation_defect_zero Q) orderSkew orderSkew_swap orderSkew_abs_le

/-- The absolute ordinary-prefix bias tends to zero in the harmonic-prefix
mixture. This is stronger than cancellation of its signed harmonic mean. -/
theorem factorSign_harmonic_prefix_abs_zero :
    Tendsto (fun N => harmonicPrefixBias N factorSign) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨Q,hQ,happrox⟩ := localFactorSign_harmonic_approximation (ε/4) (by positivity)
  have hlocal := localFactorSign_harmonic_prefix_abs_zero Q
  have htail : Tendsto (fun N => (4 : ℝ)/(harmonic (N+1) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop harmonic_real_tendsto
  filter_upwards [happrox Q le_rfl,hlocal.eventually_lt_const (by positivity : (0 : ℝ)<ε/4),
    htail.eventually_lt_const (by positivity : (0 : ℝ)<ε/4)] with N happrox hlocal htail
  have hp := harmonicPrefixBias_perturbation_bound N factorSign (localFactorSign Q)
  have herr := harmonicMean_range_error_two N (fun n => |factorSign n-localFactorSign Q n|)
    (fun n => by simpa only [abs_abs] using localFactorSign_error_le_two Q n)
  have hb := (abs_le.mp herr).2
  have hn : 0 ≤ harmonicPrefixBias N factorSign := mean_nonneg_of_nonneg _ _ (fun _ => abs_nonneg _)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hn]
  linarith

/-- Mean absolute bias of the actual ordinary sign proportions is zero on
logarithmic scales. No all-endpoint Tauberian upgrade is made. -/
theorem factorSign_prefix_absolute_harmonic_mean_zero :
    Tendsto (fun N => harmonicMean (N+1) (fun n => |prefixMean n factorSign|)) atTop (𝓝 0) :=
  harmonicMean_abs_prefix_zero_of_bias_zero factorSign
    (fun n => by simpa only [← Real.norm_eq_abs,factorSign_norm] using (le_refl (1 : ℝ)))
    factorSign_harmonic_prefix_abs_zero

theorem factorSign_prefix_square_harmonic_mean_zero :
    Tendsto (fun N => harmonicMean (N+1) (fun n => (prefixMean n factorSign)^2)) atTop (𝓝 0) := by
  apply squeeze_zero _ _ factorSign_prefix_absolute_harmonic_mean_zero
  · intro N
    unfold harmonicMean
    exact div_nonneg (sum_nonneg (fun n _ =>
      div_nonneg (sq_nonneg (prefixMean n factorSign)) (Nat.cast_nonneg n))) (harmonic_real_pos N).le
  · intro N
    apply harmonicMean_mono
    intro n
    have hb := prefixMean_unit_bound factorSign
      (fun k => by simpa only [← Real.norm_eq_abs,factorSign_norm] using (le_refl (1 : ℝ))) n
    nlinarith [abs_nonneg (prefixMean n factorSign),sq_abs (prefixMean n factorSign)]

/-- The prefix-weighted correlation contemplated in the energy argument
also vanishes. This follows from the stronger absolute-prefix theorem. -/
theorem factorSign_prefix_weighted_harmonic_mean_zero :
    Tendsto (fun N => harmonicMean (N+1) (fun n => factorSign n*prefixMean n factorSign))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm _ factorSign_prefix_absolute_harmonic_mean_zero
  intro N
  rw [Real.norm_eq_abs]
  have hb := harmonicMean_abs_le_abs_mean N (fun n => factorSign n*prefixMean n factorSign)
  have he (n : ℕ) : |factorSign n*prefixMean n factorSign| = |prefixMean n factorSign| := by
    rw [abs_mul,show |factorSign n|=1 by simpa only [← Real.norm_eq_abs] using factorSign_norm n,one_mul]
  simpa only [he] using hb

lemma factorSign_prefix_rise_proportion (n : ℕ) (hn : 0 < n) :
    prefixMean n factorSign = 2*((risingCount n : ℝ)/n-1/2) := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold prefixMean factorSign
  rw [predicateSign_sum]
  change (2*(risingCount n : ℝ)-n)/n = _
  field_simp

/-- Mean absolute deviation of the ordinary rise proportions is zero under
harmonic sampling of their endpoints. -/
theorem largest_prime_rise_proportions_harmonic_absolute_half :
    Tendsto (fun N => harmonicMean (N+1) (fun n => |(risingCount n : ℝ)/n-1/2|))
      atTop (𝓝 0) := by
  have ht := factorSign_prefix_absolute_harmonic_mean_zero.div_const 2
  simp only [zero_div] at ht
  have he (N : ℕ) : harmonicMean (N+1) (fun n => |prefixMean n factorSign|) =
      2*harmonicMean (N+1) (fun n => |(risingCount n : ℝ)/n-1/2|) := by
    unfold harmonicMean
    rw [← mul_div_assoc,mul_sum]
    congr 1
    apply sum_congr rfl
    intro n hn
    dsimp only
    rw [factorSign_prefix_rise_proportion n (mem_Icc.mp hn).1,abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ)<2),mul_div_assoc]
  simpa only [he,mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using ht

/-- For every fixed tolerance, the bad ENDPOINTS have harmonic density zero.
This does not assert that there are only finitely many bad endpoints. -/
theorem largest_prime_bad_endpoints_harmonic_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => harmonicMean (N+1) (fun n =>
      if ε ≤ |(risingCount n : ℝ)/n-1/2| then (1 : ℝ) else 0)) atTop (𝓝 0) := by
  have ht := largest_prime_rise_proportions_harmonic_absolute_half.div_const ε
  simp only [zero_div] at ht
  apply squeeze_zero _ _ ht
  · intro N
    unfold harmonicMean
    apply div_nonneg _ (harmonic_real_pos N).le
    apply sum_nonneg
    intro n _
    apply div_nonneg _ (Nat.cast_nonneg n)
    dsimp only
    split_ifs <;> norm_num
  · intro N
    have hb := harmonicMean_mono N
      (fun n => if ε ≤ |(risingCount n : ℝ)/n-1/2| then (1 : ℝ) else 0)
      (fun n => |(risingCount n : ℝ)/n-1/2|/ε) (fun n => by
        dsimp only
        split_ifs with hn
        · exact (one_le_div hε).mpr hn
        · positivity)
    have he : (fun n => |(risingCount n : ℝ)/n-1/2|/ε) =
        (fun n => ε⁻¹*|(risingCount n : ℝ)/n-1/2|) := by funext n; ring
    rw [he,harmonicMean_const_mul] at hb
    convert hb using 1
    ring

/-- Logarithmic density one of endpoints with ordinary rise proportion near
one half. The original natural-density conjecture is still stronger. -/
theorem largest_prime_near_half_endpoints_harmonic_one (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => harmonicMean (N+1) (fun n =>
      if |(risingCount n : ℝ)/n-1/2| < ε then (1 : ℝ) else 0)) atTop (𝓝 1) := by
  have ht := (largest_prime_bad_endpoints_harmonic_zero ε hε).const_sub 1
  simp only [sub_zero] at ht
  have hp (n : ℕ) : (if |(risingCount n : ℝ)/n-1/2| < ε then (1 : ℝ) else 0) =
      1-(if ε ≤ |(risingCount n : ℝ)/n-1/2| then (1 : ℝ) else 0) := by
    split_ifs <;> simp_all <;> linarith
  simpa only [hp,harmonicMean_sub,harmonicMean_one] using ht

#print axioms factorSign_prefix_absolute_harmonic_mean_zero
#print axioms factorSign_prefix_square_harmonic_mean_zero
#print axioms factorSign_prefix_weighted_harmonic_mean_zero
#print axioms largest_prime_near_half_endpoints_harmonic_one
end Erdos371
