import Submission.FractionalProfileExplore
import Submission.WeightedPushEnergyExplore

/-! Fourth-power summability and a weighted square-mass estimate for the
fractional harmonic profile. These are auxiliary necessary-condition tools. -/
namespace Erdos66FractionalFourthPower
open Filter AdditiveCombinatorics Erdos66Fractional Erdos66Generating
  Erdos66WeightedPushEnergy
open scoped Topology

lemma profile_square_bound (n : ℕ) :
    ((n : ℝ)+1)*(profile n)^2 ≤ (harmonic (n+1) : ℝ) := by
  rw [← profile_convolution]
  have hh : (∑ _ij ∈ Finset.antidiagonal n, (profile n)^2) ≤
      sumConv profile profile n := by
    apply Finset.sum_le_sum
    intro ij hij
    have he := Finset.mem_antidiagonal.mp hij
    have hi : ij.1 ≤ n := by omega
    have hj : ij.2 ≤ n := by omega
    simpa only [pow_two] using mul_le_mul (profile_antitone hi)
      (profile_antitone hj) (profile_nonneg n) (profile_nonneg ij.1)
  simpa only [Finset.sum_const,Finset.Nat.card_antidiagonal,nsmul_eq_mul,
    Nat.cast_add,Nat.cast_one] using hh

lemma eventually_harmonic_square_bound :
    ∀ᶠ n : ℕ in atTop, (harmonic (n+1) : ℝ)^2 ≤ 4*((n : ℝ)+1)^(1/2 : ℝ) := by
  have hn : Tendsto (fun n : ℕ ↦ (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ by linarith) (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlog := (Real.tendsto_log_atTop.comp hn).eventually_ge_atTop 1
  have hh := ((isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (show (0 : ℝ) < 1/2 by norm_num)).tendsto_div_nhds_zero).comp hn
  have hev := hh.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hlog,hev] with n hl hpow
  simp only [Function.comp_def,Real.rpow_two] at hpow
  have hpos : (0 : ℝ) < ((n : ℝ)+1)^(1/2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hp : (Real.log ((n : ℝ)+1))^2 ≤ ((n : ℝ)+1)^(1/2 : ℝ) := by
    have := (div_lt_iff₀ hpos).mp hpow
    linarith
  change 1 ≤ Real.log ((n : ℝ)+1) at hl
  have hH : (harmonic (n+1) : ℝ) ≤ 2*Real.log ((n : ℝ)+1) := by
    have hb := harmonic_le_one_add_log (n+1)
    simp only [Nat.cast_add,Nat.cast_one] at hb
    linarith
  have hs := pow_le_pow_left₀ (harmonic_nonneg (n+1)) hH 2
  nlinarith

/-- Although its squared sequence is not summable, the harmonic square-root
profile is in ℓ⁴. -/
lemma summable_profile_fourth : Summable (fun n ↦ (profile n)^4) := by
  have hser : Summable (fun n : ℕ ↦ 4/((n : ℝ)+1)^(3/2 : ℝ)) := by
    have hh := (Real.summable_one_div_nat_add_rpow 1 (3/2)).mpr (by norm_num)
    have habs (n : ℕ) : |(n : ℝ)+1| = (n : ℝ)+1 := abs_of_pos (by positivity)
    simpa only [habs,mul_one_div] using hh.mul_left 4
  apply hser.of_norm_bounded_eventually_nat
  filter_upwards [eventually_harmonic_square_bound] with n hn
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (profile_nonneg n) _)]
  have hnp : (0 : ℝ) < (n : ℝ)+1 := by positivity
  have hb := pow_le_pow_left₀ (by positivity : 0 ≤ ((n : ℝ)+1)*(profile n)^2)
    (profile_square_bound n) 2
  have hb' : ((n : ℝ)+1)^2*(profile n)^4 ≤ 4*((n : ℝ)+1)^(1/2 : ℝ) := by
    nlinarith
  calc
    _ ≤ 4*((n : ℝ)+1)^(1/2 : ℝ) / ((n : ℝ)+1)^2 :=
      (le_div_iff₀ (sq_pos_of_pos hnp)).mpr (by nlinarith)
    _ = 4/((n : ℝ)+1)^(3/2 : ℝ) := by
      rw [mul_div_assoc,← Real.rpow_two,← Real.rpow_sub hnp]
      norm_num
      rw [Real.rpow_neg hnp.le]
      exact (div_eq_mul_inv _ _).symm

lemma summable_profile_power_weighted {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    Summable (fun n ↦ (profile n)^k*r^n) := by
  apply (summable_geometric_of_lt_one hr0 hr1).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg (profile_nonneg n) k) (pow_nonneg hr0 n))]
  exact mul_le_of_le_one_left (pow_nonneg hr0 _) (pow_le_one₀ (profile_nonneg n) (profile_le_one n))

lemma profile_square_series_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (series (fun n ↦ (profile n)^2) r)^2*(1-r) ≤ ∑' n, (profile n)^4 := by
  have hh := tsum_cauchy_schwarz (summable_profile_power_weighted hr0 hr1 2)
    (summable_profile_power_weighted hr0 hr1 4) (summable_geometric_of_lt_one hr0 hr1)
    (fun n ↦ by positivity) (fun n ↦ pow_nonneg hr0 n) (fun n ↦ by ring)
  have hs : (∑' n, (profile n)^4*r^n) ≤ ∑' n, (profile n)^4 := by
    apply (summable_profile_power_weighted hr0 hr1 4).tsum_le_tsum _ summable_profile_fourth
    intro n
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ hr0 hr1.le)
  rw [tsum_geometric_of_lt_one hr0 hr1] at hh
  change (series (fun n ↦ (profile n)^2) r)^2 ≤ _ at hh
  have hpos := sub_pos.mpr hr1
  have hh' := mul_le_mul_of_nonneg_right hh hpos.le
  have he : ((∑' n, (profile n)^4*r^n)*(1-r)⁻¹)*(1-r)=∑' n, (profile n)^4*r^n := by
    field_simp
  rw [he] at hh'
  exact hh'.trans hs

lemma profile_square_series_limit :
    Tendsto (fun r : ℝ ↦ series (fun n ↦ (profile n)^2) r * Real.sqrt (kernel r))
      (𝓝[<] 1) (𝓝 0) := by
  have hs : Tendsto (fun r : ℝ ↦ (series (fun n ↦ (profile n)^2) r)^2 * kernel r)
      (𝓝[<] 1) (𝓝 0) := by
    apply squeeze_zero' _ _ (negative_log_one_sub.const_div_atTop (∑' n, (profile n)^4))
    · filter_upwards [unit_interval_eventually] with r hr
      exact mul_nonneg (sq_nonneg _) (kernel_pos hr.1 hr.2).le
    · filter_upwards [unit_interval_eventually] with r hr
      have hL : 0 < -Real.log (1-r) := neg_pos.mpr (Real.log_neg (by linarith [hr.2]) (by linarith [hr.1]))
      simpa only [kernel,mul_div_assoc] using div_le_div_of_nonneg_right
        (profile_square_series_bound hr.1.le hr.2) hL.le
  have hh := hs.sqrt
  simp only [Real.sqrt_zero] at hh
  apply hh.congr'
  filter_upwards [unit_interval_eventually] with r hr
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (show 0 ≤ series (fun n ↦ (profile n)^2) r from
    tsum_nonneg (fun n ↦ mul_nonneg (sq_nonneg _) (pow_nonneg hr.1.le _)))]

end Erdos66FractionalFourthPower
