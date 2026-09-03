import Submission.OneSidedMomentExplore
import Submission.ResidueEquidistributionExplore

/-! Abel comparison from coefficient prefix inequalities. -/
namespace Erdos66PrefixAbelComparison
open Filter AdditiveCombinatorics Erdos66Generating Erdos66Fractional
  Erdos66Rounding Erdos66WeightedSquareStability Erdos66ResidueSeries
open scoped Topology Classical
set_option maxHeartbeats 1500000

lemma prefix_eq_convolution (f : ℕ → ℝ) (n : ℕ) :
    prefixSum f n = sumConv f (fun _ ↦ 1) n := by
  simp only [sumConv, mul_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rfl

lemma summable_prefix {f : ℕ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hf : Summable (fun n ↦ f n*r^n)) :
    Summable (fun n ↦ prefixSum f n*r^n) := by
  simp_rw [prefix_eq_convolution]
  exact summable_weighted_convolution hf (by
    simpa only [one_mul] using summable_geometric_of_lt_one hr0 hr1)

lemma series_prefix {f : ℕ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hf : Summable (fun n ↦ f n*r^n)) :
    (1-r)*series (prefixSum f) r = series f r := by
  have hg := summable_geometric_of_lt_one hr0 hr1
  have hh := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf.norm hg.norm
  have he (n : ℕ) :
      (∑ ij ∈ Finset.antidiagonal n, (f ij.1*r^ij.1)*r^ij.2) =
        prefixSum f n*r^n := by
    rw [prefix_eq_convolution]
    simpa only [sumConv,one_mul] using weighted_convolution f (fun _ ↦ 1) r n
  simp_rw [he] at hh
  rw [tsum_geometric_of_lt_one hr0 hr1] at hh
  change series f r*(1-r)⁻¹=series (prefixSum f) r at hh
  rw [← hh]
  field_simp [(sub_pos.mpr hr1).ne']

lemma series_le_of_prefix_le (f g : ℕ → ℝ) (D : ℝ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hf : Summable (fun n ↦ f n*r^n))
    (hg : Summable (fun n ↦ g n*r^n))
    (h : ∀ n, prefixSum f n ≤ prefixSum g n+D) :
    series f r ≤ series g r+D := by
  have hp := summable_prefix hr0 hr1 hg
  have hgeom := summable_geometric_of_lt_one hr0 hr1
  have hb := (summable_prefix hr0 hr1 hf).tsum_le_tsum (fun n ↦
    mul_le_mul_of_nonneg_right (h n) (pow_nonneg hr0 n))
      (by simpa only [add_mul] using hp.add (hgeom.mul_left D))
  simp_rw [add_mul] at hb
  rw [hp.tsum_add (hgeom.mul_left D), tsum_mul_left,
    tsum_geometric_of_lt_one hr0 hr1] at hb
  change series (prefixSum f) r ≤ series (prefixSum g) r + D*(1-r)⁻¹ at hb
  have hh := mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hr1.le)
  rw [mul_add,series_prefix hr0 hr1 hf,series_prefix hr0 hr1 hg] at hh
  convert hh using 1
  field_simp [(sub_pos.mpr hr1).ne']

lemma harmonic_prefix_formula (n : ℕ) :
    prefixSum (fun i ↦ (harmonic (i+1):ℝ)) n =
      ((n:ℝ)+2)*(harmonic (n+1):ℝ)-((n:ℝ)+1) := by
  induction n with
  | zero => norm_num [prefixSum,harmonic_succ]
  | succ n ih =>
    change (∑ i ∈ Finset.range ((n+1)+1), (harmonic (i+1):ℝ)) = _
    rw [Finset.sum_range_succ]
    change prefixSum (fun i ↦ (harmonic (i+1):ℝ)) n + (harmonic (n+1+1):ℝ) = _
    rw [ih, harmonic_succ (n+1)]
    push_cast
    have hn : (n:ℝ)+1+1 ≠ 0 := by positivity
    field_simp
    ring

lemma harmonic_prefix_limit :
    Tendsto (fun n ↦ prefixSum (fun i ↦ (harmonic (i+1):ℝ)) n /
      (((n:ℝ)+1)*Real.log n)) atTop (𝓝 1) := by
  have hn : Tendsto (fun n : ℕ ↦ (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ le_add_of_nonneg_right zero_le_one)
      tendsto_natCast_atTop_atTop
  have hl := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop (1:ℝ)
  have hh := (((hn.const_div_atTop 1).const_add 1).mul harmonic_shift_log_ratio).sub hl
  norm_num only [add_zero,one_mul,sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn2
  rw [harmonic_prefix_formula]
  simp only [Function.comp_apply]
  field_simp
  ring

lemma prefix_domination_of_small_energy (f : ℕ → ℝ)
    (hf : Tendsto (fun n ↦ prefixSum f n / (((n:ℝ)+1)*Real.log n)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n, prefixSum f n ≤
      ε * prefixSum (fun i ↦ (harmonic (i+1):ℝ)) n + D := by
  have hh := hf.div harmonic_prefix_limit (by norm_num : (1:ℝ) ≠ 0)
  simp only [zero_div] at hh
  have hratio : Tendsto (fun n ↦ prefixSum f n /
      prefixSum (fun i ↦ (harmonic (i+1):ℝ)) n) atTop (𝓝 0) := by
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact div_div_div_cancel_right₀ (mul_ne_zero (by positivity)
      (Real.log_pos (by exact_mod_cast hn)).ne') _ _
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hratio.eventually_lt_const hε)
  let D := ∑ n ∈ Finset.range N, |prefixSum f n|
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  refine ⟨D,hD,fun n ↦ ?_⟩
  have hH : 0 < prefixSum (fun i ↦ (harmonic (i+1):ℝ)) n := by
    apply Finset.sum_pos'
    · intro i hi; exact harmonic_nonneg _
    · refine ⟨0,Finset.mem_range.mpr (by omega),?_⟩
      norm_num
  by_cases hn : N ≤ n
  · have := (div_lt_iff₀ hH).mp (hN n hn)
    linarith
  · have hd : |prefixSum f n| ≤ D := Finset.single_le_sum
      (f := fun k ↦ |prefixSum f k|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_range.mpr (show n < N by omega))
    have := le_abs_self (prefixSum f n)
    nlinarith

/-- Vanishing normalized cumulative mass gives vanishing normalized Abel mass.
The sequence must be nonnegative and its geometric series summable. -/
lemma abel_zero_of_prefix_limit (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n)
    (hf : Tendsto (fun n ↦ prefixSum f n / (((n:ℝ)+1)*Real.log n)) atTop (𝓝 0))
    (hs : ∀ r : ℝ, 0 < r → r < 1 → Summable (fun n ↦ f n*r^n)) :
    Tendsto (fun r ↦ series f r*kernel r) (𝓝[<] 1) (𝓝 0) := by
  have hHsum (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
      Summable (fun n ↦ (harmonic (n+1):ℝ)*r^n) :=
    summable_of_log_limit harmonic_shift_log_ratio hr0 hr1
  have hHlim : Tendsto (fun r ↦ series (fun n ↦ (harmonic (n+1):ℝ)) r*kernel r)
      (𝓝[<] 1) (𝓝 1) := by
    simpa only [kernel,mul_div_assoc] using
      logarithmic_abelian_limit harmonic_shift_log_ratio hHsum
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨D,hD,hbound⟩ := prefix_domination_of_small_energy f hf (half_pos hε)
  have hlim := (hHlim.const_mul (ε/2)).add
    (Erdos66ResidueEquidistribution.kernel_tendsto_zero.const_mul D)
  simp only [mul_one,mul_zero,add_zero] at hlim
  have hsmall := hlim.eventually_lt_const (by linarith : ε/2 < ε)
  filter_upwards [hsmall,unit_interval_eventually] with r hr hunit
  have hscaled := (hHsum r hunit.1 hunit.2).mul_left (ε/2)
  have hb := series_le_of_prefix_le f (fun n ↦ (ε/2)*(harmonic (n+1):ℝ)) D
    hunit.1.le hunit.2 (hs r hunit.1 hunit.2)
    (by simpa only [mul_assoc] using hscaled) (fun n ↦ by
      simpa only [prefixSum,← Finset.mul_sum] using hbound n)
  have hh := mul_le_mul_of_nonneg_right hb (kernel_pos hunit.1 hunit.2).le
  simp only [series,mul_assoc,tsum_mul_left] at hh
  have hnon : 0 ≤ series f r*kernel r := mul_nonneg
    (tsum_nonneg (fun n ↦ mul_nonneg (hf0 n) (pow_nonneg hunit.1.le n)))
    (kernel_pos hunit.1 hunit.2).le
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hnon]
  change series f r*kernel r ≤ ((ε/2)*series (fun n ↦ (harmonic (n+1):ℝ)) r+D)*kernel r at hh
  exact hh.trans_lt (by nlinarith [hr])

end Erdos66PrefixAbelComparison
