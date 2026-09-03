import Submission.FractionalFourthPowerExplore
import Submission.WeightedSquareStabilityExplore

/-! Any putative logarithmic representation asymptotic has unavoidable
square-root-scale fluctuations around its exact fractional harmonic model.
This necessary condition does not refute Erdős Problem 66. -/
namespace Erdos66SquareRootFluctuation
open Filter AdditiveCombinatorics Erdos66Fractional Erdos66Generating
  Erdos66FractionalFourthPower Erdos66WeightedSquareStability Erdos66ResidueSeries
open scoped Topology Classical

lemma indicator_square (A : Set ℕ) (n : ℕ) : (indicator A n)^2=indicator A n := by
  unfold indicator
  split_ifs <;> norm_num

lemma scaled_profile_convolution {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    sumConv (fun k ↦ Real.sqrt c*profile k) (fun k ↦ Real.sqrt c*profile k) n =
      c*(harmonic (n+1) : ℝ) := by
  rw [← profile_convolution]
  unfold sumConv
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  calc
    _ = (Real.sqrt c)^2*(profile ij.1*profile ij.2) := by ring
    _ = _ := by rw [Real.sq_sqrt hc]

lemma doubled_radius_limit {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun r : ℝ ↦ series (indicator A) (r^2)*Real.sqrt (kernel r))
      (𝓝[<] 1) (𝓝 (Real.sqrt c/Real.sqrt 2)) := by
  have hN : Tendsto (fun r : ℝ ↦ series (indicator A) r*Real.sqrt (kernel r))
      (𝓝[<] 1) (𝓝 (Real.sqrt c)) := witness_generating_limit h
  have hrat := witness_generating_power_ratio hc h 2 (by norm_num)
  have hh := hrat.mul hN
  simp only [Nat.cast_ofNat,one_div,inv_mul_eq_div] at hh
  apply hh.congr'
  filter_upwards [hN.eventually_ne (Real.sqrt_ne_zero'.mpr (Erdos66Explore.limit_pos hc h))] with r hr
  have hF : series (indicator A) r ≠ 0 := (mul_ne_zero_iff.mp hr).1
  field_simp

lemma weighted_error_lower_bound {A : Set ℕ} {c r : ℝ}
    (hc : 0 ≤ c) (hr0 : 0 < r) (hr1 : r < 1)
    (hE : Summable (fun n ↦ ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))^2*r^n)) :
    (max 0 (series (indicator A) (r^2) - c*series (fun n ↦ (profile n)^2) r))^2 ≤
      series (fun n ↦ ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))^2) r := by
  have hr : |r| < 1 := by rwa [abs_of_pos hr0]
  have hr2 : |r^2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_lt_one₀ hr0.le hr1 (by norm_num)
  have hf2 : Summable (fun n ↦ (indicator A n)^2*(r^2)^n) := by
    simp_rw [indicator_square]
    exact summable_indicator A hr2
  have hg : Summable (fun n ↦ (Real.sqrt c*profile n)*r^n) := by
    simpa only [pow_one,mul_assoc] using (summable_profile_power_weighted hr0.le hr1 1).mul_left (Real.sqrt c)
  have hg2 : Summable (fun n ↦ (Real.sqrt c*profile n)^2*r^n) := by
    simpa only [mul_pow,Real.sq_sqrt hc,mul_assoc] using (summable_profile_power_weighted hr0.le hr1 2).mul_left c
  have hcA (n : ℕ) : sumConv (indicator A) (indicator A) n = (sumRep A n : ℝ) :=
    sum_indicator_antidiagonal A n
  have hEc : Summable (fun n ↦ (sumConv (indicator A) (indicator A) n -
      sumConv (fun n ↦ Real.sqrt c*profile n) (fun n ↦ Real.sqrt c*profile n) n)^2*r^n) := by
    simpa only [hcA,scaled_profile_convolution hc] using hE
  have hh := weighted_square_stability_limit hr0.le hr1 (indicator_nonneg A)
    (summable_indicator A hr) hg hf2 hg2 hEc
  simpa only [indicator_square,mul_pow,Real.sq_sqrt hc,mul_assoc,tsum_mul_left,
    hcA,scaled_profile_convolution hc,series] using hh

/-- If the harmonic-centered squared error has a logarithmic mean scale d,
that constant must be at least c/2. No convergence of squared error is
assumed in the original conjecture. -/
theorem squared_error_limit_lower_bound {A : Set ℕ} {c d : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (he : Tendsto (fun n ↦ ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))^2/Real.log n)
      atTop (𝓝 d)) : c/2 ≤ d := by
  have hcpos := Erdos66Explore.limit_pos hc h
  have hleft0 := (doubled_radius_limit hc h).sub (profile_square_series_limit.const_mul c)
  simp only [mul_zero,sub_zero] at hleft0
  have hleft := ((show Tendsto (fun _ : ℝ ↦ (0 : ℝ)) (𝓝[<] 1) (𝓝 0) from tendsto_const_nhds).max hleft0).pow 2
  have hspos : 0 < Real.sqrt c/Real.sqrt 2 := div_pos (Real.sqrt_pos.mpr hcpos) (by positivity)
  rw [max_eq_right hspos.le,div_pow,Real.sq_sqrt hcpos.le,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)] at hleft
  have hright : Tendsto (fun r : ℝ ↦ series (fun n ↦ ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))^2) r * kernel r)
      (𝓝[<] 1) (𝓝 d) := by
    simpa only [kernel,mul_div_assoc] using logarithmic_abelian_limit he
      (fun r hr0 hr1 ↦ summable_of_log_limit he hr0 hr1)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [unit_interval_eventually] with r hr
  have hk := (kernel_pos hr.1 hr.2).le
  have hb := mul_le_mul_of_nonneg_right
    (weighted_error_lower_bound hcpos.le hr.1 hr.2 (summable_of_log_limit he hr.1 hr.2)) hk
  have hs := Real.sq_sqrt hk
  have heq : (max 0 (series (indicator A) (r^2)*Real.sqrt (kernel r) -
      c*(series (fun n ↦ (profile n)^2) r*Real.sqrt (kernel r))))^2 =
      (max 0 (series (indicator A) (r^2)-c*series (fun n ↦ (profile n)^2) r))^2*kernel r := by
    calc
      _ = (max 0 (series (indicator A) (r^2)-c*series (fun n ↦ (profile n)^2) r)*Real.sqrt (kernel r))^2 := by
        rw [max_mul_of_nonneg _ _ (Real.sqrt_nonneg _),zero_mul,sub_mul]
        congr 2
        ring
      _ = _ := by rw [mul_pow,hs]
  rw [heq]
  exact hb

/-- The conjectural relative error may tend to zero, but it cannot do so
faster than the square-root logarithmic fluctuation scale. -/
theorem not_squared_error_little_o_log {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    ¬ Tendsto (fun n ↦ ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))^2/Real.log n)
      atTop (𝓝 0) := by
  intro he
  have hh := squared_error_limit_lower_bound hc h he
  have hp := Erdos66Explore.limit_pos hc h
  linarith

end Erdos66SquareRootFluctuation
