import Submission.DampedMeanZeta

/-! One-variable means of absolutely convergent divisor convolutions, and
in particular the full fixed-parameter smoothed Mangoldt mean. -/
namespace Erdos972DampedSingleMean

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972UniformDampedTail Erdos972SmoothMangoldt
open Erdos972FixedDampedCorrelation Erdos972SmoothDivisorTail

lemma divisor_prefix_expansion (a : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, a d) =
      ∑ d ∈ Ioc 0 N, a d*(N/d : ℕ) := by
  classical
  rw [sum_congr rfl (fun n hn => divisor_sum_box hn a), sum_comm]
  apply sum_congr rfl
  intro d _
  rw [← sum_filter, sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div, mul_comm]

lemma divisor_average_eq_tsum (a : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, a d)/(N : ℝ) =
      ∑' d : ℕ, a d*(N/d : ℕ)/(N : ℝ) := by
  rw [divisor_prefix_expansion, sum_div, tsum_eq_sum (s := Ioc 0 N)]
  intro d hd
  by_cases hd0 : d = 0
  · simp [hd0]
  have hNd : N < d := by simpa only [mem_Ioc, Nat.pos_of_ne_zero hd0, true_and, not_le] using hd
  simp [Nat.div_eq_of_lt hNd]

lemma nat_div_ratio_tendsto (d : ℕ) :
    Tendsto (fun N : ℕ => ((N/d : ℕ) : ℝ)/(N : ℝ)) atTop (𝓝 (1/(d : ℝ))) := by
  by_cases hd : d = 0
  · simp [hd]
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero_norm' _ (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hlo : ((N/d : ℕ) : ℝ) ≤ (N : ℝ)/d := Nat.cast_div_le
  have hhi : (N : ℝ) ≤ (d : ℝ)*((N/d : ℕ)+1) := by
    exact_mod_cast (Nat.lt_mul_div_succ N (Nat.pos_of_ne_zero hd)).le
  have hratio : ((N/d : ℕ) : ℝ)/(N : ℝ) ≤ 1/(d : ℝ) := by
    apply (div_le_div_iff₀ hNR hdR).mpr
    nlinarith only [(le_div_iff₀ hdR).mp hlo]
  simp only [Real.norm_eq_abs, abs_abs]
  rw [abs_of_nonpos (sub_nonpos.mpr hratio)]
  apply (le_div_iff₀ hNR).mpr
  have hN0 : (N : ℝ) ≠ 0 := hNR.ne'
  field_simp
  nlinarith only [hhi]

lemma divisor_average_term_bound (a : ℕ → ℝ) (N d : ℕ) :
    ‖a d*(N/d : ℕ)/(N : ℝ)‖ ≤ ‖a d/(d : ℝ)‖ := by
  by_cases hN : N = 0
  · subst N
    simp only [Nat.zero_div, Nat.cast_zero, mul_zero, div_zero, norm_zero]
    exact norm_nonneg _
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  simp only [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (N/d)),
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N), abs_of_nonneg (Nat.cast_nonneg (α := ℝ) d)]
  calc
    _ ≤ (|a d| *((N : ℝ)/d))/(N : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left Nat.cast_div_le (abs_nonneg _)) hNR.le
    _ = _ := by field_simp

/-- An elementary absolutely convergent divisor mean theorem. -/
theorem divisor_mean_tendsto (a : ℕ → ℝ) (ha : Summable (fun d : ℕ => a d/d)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, a d)/(N : ℝ))
      atTop (𝓝 (∑' d : ℕ, a d/d)) := by
  simp_rw [divisor_average_eq_tsum]
  apply tendsto_tsum_of_dominated_convergence ha.norm
  · intro d
    simpa only [← mul_div_assoc, mul_one] using (nat_div_ratio_tendsto d).const_mul (a d)
  · exact Eventually.of_forall (fun N d => divisor_average_term_bound a N d)

lemma expDivisorSum_mean_tendsto {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, expDivisorSum t n)/(N : ℝ))
      atTop (𝓝 (dampedMean t)) := by
  exact divisor_mean_tendsto (dampedCoefficient t) (summable_dampedMean ht)

lemma smooth_sum_identity (t : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Ioc 0 N, smoothMangoldt t n) =
      ((∑ n ∈ Ioc 0 N, expDivisorSum t n)-1)/t := by
  simp only [smoothMangoldt, expDivisorSum_at_zero, one_apply, ← sum_div, sum_sub_distrib]
  simp [hN]

/-- The full one-variable mean exists for every fixed positive parameter,
without passing to selected irrational scales. -/
theorem smoothMangoldt_mean_tendsto {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, smoothMangoldt t n)/(N : ℝ))
      atTop (𝓝 (dampedMean t/t)) := by
  have hh := ((expDivisorSum_mean_tendsto ht).sub
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))).div_const t
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  rw [smooth_sum_identity t hN]
  ring

#print axioms divisor_mean_tendsto
#print axioms smoothMangoldt_mean_tendsto

end Erdos972DampedSingleMean
