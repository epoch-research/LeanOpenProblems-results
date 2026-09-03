import Submission.GlobalTwoScaleMinorant
import Submission.MixedSmoothMean
import Submission.FullSmoothL1Obstruction

/-! The size-dependent minorant removes the validity window, but its actual
fixed-parameter smooth-weighted mean is negative for small parameters.
This is not a proof or disproof of Erdos 972. -/
namespace Erdos972GlobalTwoScaleMean

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972GlobalTwoScaleMinorant Erdos972MixedSmoothMean
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive
open Erdos972FullSmoothL1Obstruction Erdos972DampedMeanZeta
open Erdos972FixedDampedCorrelation Erdos972PrimePowerError
open Erdos972ExponentialSum

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The damped form of the current global minorant. -/
noncomputable def dampedLower (t : ℝ) (n : ℕ) : ℝ :=
  (1 + halfDamping t n)^2 * smoothMangoldt t n / 2 - smoothMangoldt (2*t) n

lemma dampedLower_eq_halfDamping_mul {t : ℝ} (ht : 0 < t) (n : ℕ) :
    dampedLower t n = halfDamping t n * globalMinorant t n := by
  by_cases hn : n = 1
  · simp [hn, dampedLower, globalMinorant, smoothMangoldt, expDivisorSum]
  rw [dampedLower, globalMinorant, if_neg hn, smoothMangoldt, smoothMangoldt,
    expDivisorSum_at_zero, one_apply, if_neg hn, sub_zero]
  have hz := (halfDamping_pos t n).ne'
  field_simp
  ring

lemma halfDamping_le_one {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : halfDamping t n ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (div_nonneg ht (by norm_num))) (Real.log_natCast_nonneg n)

lemma halfDamping_tendsto {t : ℝ} (ht : 0 < t) :
    Tendsto (halfDamping t) atTop (𝓝 0) := by
  have hl : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hh := Real.tendsto_exp_atBot.comp
    (hl.const_mul_atTop_of_neg (show -t/2 < 0 by linarith))
  convert hh using 1
  funext n
  unfold halfDamping
  congr 1
  ring

lemma cesaro_Ioc_zero {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, f n)/(N : ℝ)) atTop (𝓝 0) := by
  have hh := (hf.comp (tendsto_add_atTop_nat 1)).cesaro
  simpa only [sum_Ioc_zero_eq_sum_range_succ, Function.comp_apply,
    div_eq_mul_inv, mul_comm] using hh

noncomputable def correctionTerm (s t α : ℝ) (n : ℕ) : ℝ :=
  smoothMangoldt s n *
    ((halfDamping t (floorMul α n)+(halfDamping t (floorMul α n))^2/2)*
      smoothMangoldt t (floorMul α n))

lemma correctionTerm_tendsto {α s t : ℝ} (hα : 1 ≤ α) (hs : 0 < s) (ht : 0 < t) :
    Tendsto (correctionTerm s t α) atTop (𝓝 0) := by
  have hg : Tendsto (floorMul α) atTop atTop :=
    tendsto_atTop_mono (self_le_floorMul hα) tendsto_id
  have hh := ((halfDamping_tendsto ht).comp hg).const_mul (2/(s*t))
  simp only [mul_zero] at hh
  apply squeeze_zero' _ _ hh
  · filter_upwards with n
    unfold correctionTerm
    exact mul_nonneg (smoothMangoldt_nonneg hs n)
      (mul_nonneg (by positivity [halfDamping_pos t (floorMul α n)])
        (smoothMangoldt_nonneg ht _))
  · filter_upwards with n
    let x := halfDamping t (floorMul α n)
    have hx0 : 0 ≤ x := (halfDamping_pos _ _).le
    have hx1 : x ≤ 1 := halfDamping_le_one ht.le _
    have hxc : x+x^2/2 ≤ 2*x := by nlinarith only [hx0, hx1, mul_nonneg hx0 (sub_nonneg.mpr hx1)]
    have hp : smoothMangoldt s n * smoothMangoldt t (floorMul α n) ≤ 1/(s*t) := by
      simpa only [div_mul_div_comm, one_mul] using
        mul_le_mul (smoothMangoldt_le_inv hs n) (smoothMangoldt_le_inv ht (floorMul α n))
          (smoothMangoldt_nonneg ht (floorMul α n)) (by positivity : 0 ≤ 1/s)
    have hp0 := mul_nonneg (smoothMangoldt_nonneg hs n) (smoothMangoldt_nonneg ht (floorMul α n))
    have hb := mul_le_mul hxc hp hp0 (by positivity : 0 ≤ 2*x)
    change correctionTerm s t α n ≤ 2/(s*t)*x
    unfold correctionTerm
    change smoothMangoldt s n*((x+x^2/2)*smoothMangoldt t (floorMul α n)) ≤ _
    convert hb using 1 <;> ring

noncomputable def mixedDampedLower (s t α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, smoothMangoldt s n * dampedLower t (floorMul α n)

noncomputable def mixedDampedLowerMean (s t : ℝ) : ℝ :=
  (dampedMean s/s)*((dampedMean t/t)/2-dampedMean (2*t)/(2*t))

lemma mixedDampedLower_decompose (s t α : ℝ) (N : ℕ) :
    mixedDampedLower s t α N =
      mixedSmoothCorrelation s t α N/2-mixedSmoothCorrelation s (2*t) α N+
        ∑ n ∈ Ioc 0 N, correctionTerm s t α n := by
  unfold mixedDampedLower mixedSmoothCorrelation
  rw [sum_div, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  unfold dampedLower correctionTerm
  ring

/-- The fixed-parameter mean is proved for the actual signed sum, not just
for a formal scalar benchmark. -/
theorem mixedDampedLower_fixed_mean {α s t : ℝ} (hα : 1 ≤ α) (hI : Irrational α)
    (hs : 0 < s) (ht : 0 < t) :
    Tendsto (fun N : ℕ => mixedDampedLower s t α N/(N : ℝ)) atTop
      (𝓝 (mixedDampedLowerMean s t)) := by
  have h₁ := mixed_smooth_mean hα hI hs ht
  have h₂ := mixed_smooth_mean hα hI hs (show 0 < 2*t by positivity)
  have h₃ := cesaro_Ioc_zero (correctionTerm_tendsto hα hs ht)
  have hh := ((h₁.div_const 2).sub h₂).add h₃
  convert hh using 1
  · funext N
    rw [mixedDampedLower_decompose]
    ring
  · unfold mixedDampedLowerMean
    congr 1
    ring

/-- In contrast to the small-window minorant's scalar mean, the new global
minorant has a negative iterated mean. -/
theorem diagonal_mean_tendsto :
    Tendsto (fun t : ℝ => mixedDampedLowerMean t t) (𝓝[>] 0) (𝓝 (-1/2 : ℝ)) := by
  have h₁ := dampedMean_div_tendsto_one
  have h₂ := dampedMean_div_tendsto_one.comp double_parameter_tendsto
  have hh := h₁.mul ((h₁.div_const 2).sub h₂)
  norm_num only [one_mul] at hh
  convert hh using 1; norm_num [mixedDampedLowerMean]

/-- Hence this window-free weight supplies no positive fixed-parameter
smooth-weighted mean at small parameters. -/
theorem eventually_negative_fixed_mean {α : ℝ} (hα : 1 ≤ α) (hI : Irrational α) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ᶠ N : ℕ in atTop,
      mixedDampedLower t t α N < -(N : ℝ)/4 := by
  have hm := (tendsto_order.mp diagonal_mean_tendsto).2 (-1/3) (by norm_num)
  filter_upwards [self_mem_nhdsWithin, hm] with t ht hm
  change 0 < t at ht
  have hh := (tendsto_order.mp (mixedDampedLower_fixed_mean hα hI ht ht)).2
    (-1/4) (show mixedDampedLowerMean t t < -1/4 by linarith only [hm])
  filter_upwards [hh, eventually_ge_atTop (1 : ℕ)] with N hN hNpos
  have he := (div_lt_iff₀ (Nat.cast_pos.mpr hNpos : (0 : ℝ) < N)).mp hN
  linarith only [he]

#print axioms mixedDampedLower_fixed_mean
#print axioms diagonal_mean_tendsto
#print axioms eventually_negative_fixed_mean

end Erdos972GlobalTwoScaleMean
