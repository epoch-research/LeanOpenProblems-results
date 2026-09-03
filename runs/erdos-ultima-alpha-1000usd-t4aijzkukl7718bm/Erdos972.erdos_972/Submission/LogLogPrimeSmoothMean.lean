import Submission.PrimeSmoothMeanScales
import Submission.DampedMeanTailBound

/-! A moving prime-input / smooth-output mean, with t of order
log(log N)/log N. This range still does not detect prime outputs. -/
namespace Erdos972LogLogPrimeSmoothMean

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972PrimeSmoothMeanScales Erdos972PrimeLeastFactorScales
open Erdos972PrimeRoughOutputs Erdos972PrimePowerError Erdos972SmoothDivisorTail
open Erdos972FixedDampedCorrelation Erdos972DivisorCovariance
open Erdos972ExactLargeDivisorFirstMoment Erdos972PolynomialRowScales
open Erdos972SelbergLowerTest Erdos972ChebyshevPNT Erdos972DampedMeanTailBound
open Erdos972DampedMeanZeta Erdos972GrowingCoprimeCandidates Erdos972DualPrimeRows
open Erdos972ScaledPrimeRows

set_option autoImplicit false
set_option maxHeartbeats 3000000
attribute [local irreducible] root64

noncomputable def logScale (u : ℕ) : ℝ := 1+Real.log u

lemma logScale_one_le (u : ℕ) : 1 ≤ logScale u := by
  unfold logScale
  linarith only [Real.log_natCast_nonneg u]

lemma logScale_pos (u : ℕ) : 0 < logScale u := lt_of_lt_of_le zero_lt_one (logScale_one_le u)

lemma logScale_tendsto : Tendsto logScale atTop atTop := by
  apply tendsto_atTop_mono (fun u : ℕ => show Real.log u ≤ logScale u by unfold logScale; linarith)
  exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma inverse_logScale_tendsto : Tendsto (fun u : ℕ => 1/logScale u) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop logScale_tendsto

noncomputable def loglogParameter (u : ℕ) : ℝ :=
  520*Real.log (1+logScale u)/logScale u

lemma loglogParameter_pos (u : ℕ) : 0 < loglogParameter u := by
  unfold loglogParameter
  exact div_pos (mul_pos (by norm_num) (Real.log_pos (by linarith only [logScale_pos u])))
    (logScale_pos u)

lemma loglogParameter_inverse_le (u : ℕ) : 1/loglogParameter u ≤ logScale u := by
  have hl := Real.log_le_log (by norm_num : (0:ℝ) < 2)
    (show (2:ℝ) ≤ 1+logScale u by linarith only [logScale_one_le u])
  have hlog : 1 ≤ 520*Real.log (1+logScale u) := by linarith only [hl, Real.log_two_gt_d9]
  apply (div_le_iff₀ (loglogParameter_pos u)).mpr
  simpa only [loglogParameter, mul_div_cancel₀ _ (logScale_pos u).ne', mul_div_cancel_left₀ _ (logScale_pos u).ne'] using hlog

lemma loglogParameter_tendsto : Tendsto loglogParameter atTop (𝓝 0) := by
  have hplus : Tendsto (fun u : ℕ => 1+logScale u) atTop atTop := by
    apply tendsto_atTop_mono (fun u => show logScale u ≤ 1+logScale u by linarith) logScale_tendsto
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hplus
  have hratio := inverse_logScale_tendsto.const_add 1
  have hh := (hlog.mul hratio).const_mul 520
  simp only [add_zero, zero_mul, mul_zero] at hh
  apply hh.congr'
  filter_upwards with u
  dsimp only [Function.comp_def, id_eq]
  unfold loglogParameter
  have hu := (logScale_pos u).ne'
  have hu1 : 1+logScale u ≠ 0 := by linarith only [logScale_pos u]
  field_simp
  ring

lemma loglogParameter_tendsto_right : Tendsto loglogParameter atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨loglogParameter_tendsto,
    Eventually.of_forall (fun u => loglogParameter_pos u)⟩

lemma loglog_damping_bound {u : ℕ} (hu : 0 < u) (hL : 130 ≤ logScale u) :
    damping (loglogParameter u) (root64 u) ≤ 1/(logScale u)^4 := by
  have hroot := root64_log_bound hu
  have hr : logScale u/130 ≤ Real.log (root64 u) := by
    change logScale u ≤ 65*(1+Real.log (root64 u)) at hroot
    linarith only [hL, hroot]
  have hm := mul_le_mul_of_nonneg_left hr (loglogParameter_pos u).le
  have he : loglogParameter u*(logScale u/130) = 4*Real.log (1+logScale u) := by
    unfold loglogParameter
    field_simp
    ring
  rw [he] at hm
  have hlog := Real.log_le_log (logScale_pos u) (show logScale u ≤ 1+logScale u by linarith)
  have heq : Real.exp (-4*Real.log (logScale u)) = 1/(logScale u)^4 := by
    rw [show -4*Real.log (logScale u) = -(Real.log (logScale u)*4) by ring,
      Real.exp_neg, ← Real.rpow_def_of_pos (logScale_pos u)]
    norm_num only [Real.rpow_ofNat]
    simp only [one_div]
  rw [← heq]
  apply Real.exp_le_exp.mpr
  linarith only [hm, hlog]

lemma loglog_damping_inverse_square {u : ℕ} (hu : 0 < u) (hL : 130 ≤ logScale u) :
    damping (loglogParameter u) (root64 u)/(loglogParameter u)^2 ≤ 1/(logScale u)^2 := by
  have hd := loglog_damping_bound hu hL
  have hi := loglogParameter_inverse_le u
  have he : damping (loglogParameter u) (root64 u)/(loglogParameter u)^2 =
      damping (loglogParameter u) (root64 u)*(1/loglogParameter u)^2 := by ring
  rw [he]
  calc
    _ ≤ (1/(logScale u)^4)*(logScale u)^2 := by gcongr; positivity [loglogParameter_pos u]
    _ = _ := by field_simp

lemma loglog_damping_weight {u : ℕ} (hu : 0 < u) (hL : 130 ≤ logScale u) :
    damping (loglogParameter u) (root64 u)*(logScale u)^2/loglogParameter u ≤ 1/logScale u := by
  have hd := loglog_damping_bound hu hL
  have hi := loglogParameter_inverse_le u
  have he : damping (loglogParameter u) (root64 u)*(logScale u)^2/loglogParameter u =
      damping (loglogParameter u) (root64 u)*(logScale u)^2*(1/loglogParameter u) := by ring
  rw [he]
  calc
    _ ≤ (1/(logScale u)^4)*(logScale u)^2*logScale u := by gcongr; positivity [loglogParameter_pos u]
    _ = _ := by field_simp

lemma loglog_divisorMean_tendsto :
    Tendsto (fun u : ℕ => divisorMean (root64 u) (dampedCoefficient (loglogParameter u))/
      loglogParameter u) atTop (𝓝 1) := by
  have hA := dampedMean_div_tendsto_one.comp loglogParameter_tendsto_right
  have hi : Tendsto (fun u : ℕ => 1/(logScale u)^2) atTop (𝓝 0) := by
    simpa only [div_pow, one_pow, zero_pow (by decide : 2 ≠ 0)] using inverse_logScale_tendsto.pow 2
  have he : Tendsto (fun u : ℕ =>
      divisorMean (root64 u) (dampedCoefficient (loglogParameter u))/loglogParameter u-
      dampedMean (loglogParameter u)/loglogParameter u) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hi
    filter_upwards [eventually_ge_atTop (1:ℕ), logScale_tendsto.eventually_ge_atTop 130] with u hu hL
    have ht := loglogParameter_pos u
    have hb := div_le_div_of_nonneg_right (dampedMean_tail_bound ht (root64_bounds hu).1) ht.le
    rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos ht]
    apply hb.trans
    simpa only [div_div, pow_two] using loglog_damping_inverse_square hu hL
  simpa only [sub_add_cancel, zero_add, Function.comp_def] using he.add hA

lemma logScale_div_self_tendsto :
    Tendsto (fun u : ℕ => logScale u/(u:ℝ)) atTop (𝓝 0) := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun u : ℕ => 1/(u:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa only [logScale, add_div, Function.comp_def, id_eq, add_zero] using hi.add hlog

lemma primePower_log_weight_tendsto :
    Tendsto (fun u : ℕ => (root64 u:ℝ)*logScale u*
      (Chebyshev.psi (u^6:ℕ)-Chebyshev.theta (u^6:ℕ))/(u:ℝ)^6) atTop (𝓝 0) := by
  let C : ℝ := Real.log 4+12
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hi : Tendsto (fun u : ℕ => 1/(u:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim := (logScale_div_self_tendsto.mul hi).const_mul C
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun u => by
    exact div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (logScale_pos u).le)
      (sub_nonneg.mpr (Chebyshev.theta_le_psi _))) (by positivity))) _ hlim
  filter_upwards [eventually_ge_atTop (1:ℕ)] with u hu
  have huR : (0:ℝ) < u := Nat.cast_pos.mpr hu
  have hN : (1:ℝ) ≤ (u^6:ℕ) := by exact_mod_cast Nat.one_le_pow 6 u hu
  have he := psi_sub_theta_le_sqrt hN
  have hs : Real.sqrt ((u^6:ℕ):ℝ) = (u:ℝ)^3 := by
    rw [Nat.cast_pow, show (u:ℝ)^6 = ((u:ℝ)^3)^2 by ring, Real.sqrt_sq (by positivity)]
  rw [hs] at he
  change _ ≤ C*(u:ℝ)^3 at he
  have hv : (root64 u:ℝ) ≤ u := Nat.cast_le.mpr (root64_le_self u)
  have hL0 := (logScale_pos u).le
  have hP0 := sub_nonneg.mpr (Chebyshev.theta_le_psi ((u^6:ℕ):ℝ))
  calc
    _ ≤ (u:ℝ)*logScale u*(C*(u:ℝ)^3)/(u:ℝ)^6 := by
      gcongr
    _ = _ := by field_simp

lemma primeRowError_log_weight_tendsto :
    Tendsto (fun u : ℕ => (root64 u:ℝ)*logScale u*primeRowError u/(u:ℝ)^6) atTop (𝓝 0) := by
  have hh := (summed_scaledRowError_tendsto 1 1).add primePower_log_weight_tendsto
  simpa only [primeRowError, logScale, pow_one, mul_add, add_div, add_zero] using hh

lemma loglog_row_error_tendsto :
    Tendsto (fun u : ℕ => ((root64 u:ℝ)*primeRowError u/(u:ℝ)^6)/loglogParameter u)
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun u => by
    positivity [primeRowError_nonneg u, loglogParameter_pos u])) _ primeRowError_log_weight_tendsto
  filter_upwards with u
  have hh := mul_le_mul_of_nonneg_left (loglogParameter_inverse_le u)
    (show 0 ≤ (root64 u:ℝ)*primeRowError u/(u:ℝ)^6 by positivity [primeRowError_nonneg u])
  convert hh using 1 <;> ring

lemma loglog_primeSmoothMain_tendsto :
    Tendsto (fun u : ℕ => primeSmoothMain (loglogParameter u) u) atTop (𝓝 1) := by
  have hpow : Tendsto (fun u : ℕ => u^6) atTop atTop := tendsto_pow_atTop (by decide)
  have hpsi := psi_div_self_tendsto.comp (tendsto_natCast_atTop_atTop.comp hpow)
  have hh := hpsi.mul loglog_divisorMean_tendsto
  unfold primeSmoothMain
  simpa only [Function.comp_def, Nat.cast_pow, one_mul] using hh

noncomputable def loglogErrorBudget (α : ℝ) (u : ℕ) : ℝ :=
  ((root64 u:ℝ)*primeRowError u/(u:ℝ)^6)/loglogParameter u+
    42*α/logScale u+|primeSmoothMain (loglogParameter u) u-1|

lemma loglogErrorBudget_tendsto (α : ℝ) : Tendsto (loglogErrorBudget α) atTop (𝓝 0) := by
  have hd := inverse_logScale_tendsto.const_mul (42*α)
  have hm := (loglog_primeSmoothMain_tendsto.sub_const 1).abs
  have hh := (loglog_row_error_tendsto.add hd).add hm
  unfold loglogErrorBudget
  simpa only [mul_one_div, mul_zero, sub_self, abs_zero, zero_add, add_zero] using hh

lemma loglog_prime_smooth_error {α : ℝ} (hα : 1 ≤ α) {u : ℕ}
    (hu : 0 < u) (hαu : α ≤ u) (hL : 130 ≤ logScale u)
    (hrows : ∀ d : ℕ, 0 < d → d ≤ root64 u →
      |row (Ioc 0 (u^6)) primeWeight (floorMul α) d-Chebyshev.psi (u^6:ℕ)/(d:ℝ)| ≤ primeRowError u) :
    |mixedPrimeSmooth (loglogParameter u) α (u^6)/(u:ℝ)^6-1| ≤ loglogErrorBudget α u := by
  have hh := prime_smooth_normalized_error hα (loglogParameter_pos u) hu hαu hrows
  have hd := mul_le_mul_of_nonneg_left (loglog_damping_weight hu hL)
    (show 0 ≤ 42*α by linarith only [hα])
  have hb : ((root64 u:ℝ)*primeRowError u/(u:ℝ)^6+
      42*α*damping (loglogParameter u) (root64 u)*(1+Real.log u)^2)/loglogParameter u ≤
      ((root64 u:ℝ)*primeRowError u/(u:ℝ)^6)/loglogParameter u+42*α/logScale u := by
    have he := add_le_add_right hd (((root64 u:ℝ)*primeRowError u/(u:ℝ)^6)/loglogParameter u)
    dsimp only [logScale] at he ⊢
    convert he using 1 <;> ring
  exact (abs_sub_le (mixedPrimeSmooth (loglogParameter u) α (u^6)/(u:ℝ)^6)
    (primeSmoothMain (loglogParameter u) u) 1).trans
      (add_le_add_left (hh.trans hb) _)

/-- The parameter now moves with the ACTUAL chosen scale. -/
theorem exists_loglog_prime_smooth_mean_scale {α ε : ℝ} (hα : 1 < α) (hI : Irrational α)
    (hε : 0 < ε) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ 0 < u ∧
      |mixedPrimeSmooth (loglogParameter u) α (u^6)/(u:ℝ)^6-1| < ε := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((tendsto_order.mp (loglogErrorBudget_tendsto α)).2 ε hε).and
      ((logScale_tendsto.eventually_ge_atTop 130).and (eventually_ge_atTop ⌈α⌉₊)))
  obtain ⟨u, hBu, hu, _, hrows⟩ :=
    exists_small_prime_prefix_rows hα hI (by norm_num : (0:ℝ) < 1) (max B T)
  obtain ⟨he, hL, hαu⟩ := hT u ((le_max_right B T).trans hBu.le)
  have hαu' : α ≤ u := (Nat.le_ceil α).trans (Nat.cast_le.mpr hαu)
  refine ⟨u, (le_max_left B T).trans_lt hBu, hu, ?_⟩
  exact (loglog_prime_smooth_error hα.le hu hαu' hL
    (fun d hd hdv => hrows d hd hdv (u^6) le_rfl)).trans_lt he

/-- The output weight is positive at arbitrarily large actual good scales. -/
theorem exists_loglog_prime_smooth_positive_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    (B : ℕ) :
    ∃ u : ℕ, B < u ∧ (u:ℝ)^6/2 < mixedPrimeSmooth (loglogParameter u) α (u^6) := by
  obtain ⟨u, hBu, hu, he⟩ := exists_loglog_prime_smooth_mean_scale hα hI
    (by norm_num : (0:ℝ) < 1/2) B
  have hh := (abs_lt.mp he).1
  have hlo : (1:ℝ)/2 < mixedPrimeSmooth (loglogParameter u) α (u^6)/(u:ℝ)^6 := by
    linarith only [hh]
  have hNR : (0:ℝ) < (u:ℝ)^6 := pow_pos (Nat.cast_pos.mpr hu) _
  refine ⟨u, hBu, ?_⟩
  simpa only [one_div_mul_eq_div] using (lt_div_iff₀ hNR).mp hlo

/-- This confirms explicitly that the new parameter remains outside every
bounded t*log(N) prime-detection window. -/
theorem loglogParameter_log_cutoff_tendsto :
    Tendsto (fun u : ℕ => loglogParameter u*Real.log (u^6:ℕ)) atTop atTop := by
  have hplus : Tendsto (fun u : ℕ => 1+logScale u) atTop atTop :=
    tendsto_atTop_mono (fun u => by linarith : ∀ u : ℕ, logScale u ≤ 1+logScale u) logScale_tendsto
  have hlog := Real.tendsto_log_atTop.comp hplus
  have hmain := hlog.const_mul_atTop (by norm_num : (0:ℝ) < 1560)
  apply tendsto_atTop_mono' atTop _ hmain
  filter_upwards [logScale_tendsto.eventually_ge_atTop 2] with u hL
  have ht := loglogParameter_pos u
  have hlogu : logScale u/2 ≤ Real.log u := by unfold logScale at *; linarith only [hL]
  have hh := mul_le_mul_of_nonneg_left hlogu ht.le
  have he : loglogParameter u*(logScale u/2) = 260*Real.log (1+logScale u) := by
    unfold loglogParameter
    field_simp
    ring
  rw [he] at hh
  rw [Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  dsimp only [Function.comp_def]
  nlinarith only [hh]

#print axioms loglogParameter_log_cutoff_tendsto
#print axioms loglog_divisorMean_tendsto
#print axioms loglogErrorBudget_tendsto
#print axioms exists_loglog_prime_smooth_mean_scale

end Erdos972LogLogPrimeSmoothMean
