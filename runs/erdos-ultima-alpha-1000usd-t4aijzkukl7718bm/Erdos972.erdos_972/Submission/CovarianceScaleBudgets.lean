import Submission.OriginalTypeICovariance
import Submission.TypeICovarianceScales

/-! Transfer of all three covariance budgets to the common main cutoff. -/
namespace Erdos972CovarianceScaleBudgets

open Filter Finset ArithmeticFunction
open scoped Topology
open Erdos972CenteredRowScales Erdos972PolynomialRowScales Erdos972GrowingTypeI
open Erdos972TypeICovarianceScales Erdos972GrowingTypeIIReduction
open Erdos972DualPrimeRows Erdos972ScaledPrimeRows Erdos972DualProfileCovariance
open Erdos972LogarithmicCovariance Erdos972RealLogCenter Erdos972MobiusPartialSums

set_option maxHeartbeats 1000000

lemma scaleCutoff_tendsto {α : ℝ} (hα : 1 ≤ α) : Tendsto (scaleCutoff α) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [eventually_ge_atTop (max B (max 1 ⌈α⌉₊))] with u hu
  have hu0 : 0 < u := (le_max_left 1 _).trans ((le_max_right B _).trans hu)
  have hαu : α ≤ u := (Nat.le_ceil α).trans (Nat.cast_le.mpr
    ((le_max_right 1 _).trans ((le_max_right B _).trans hu)))
  exact ((le_max_left B _).trans hu).trans (scaleCutoff_bounds hα hu0 hαu).1

lemma scale_log_bound {α : ℝ} (hα : 1 ≤ α) {u : ℕ} (hu : 0 < u) (hαu : α ≤ u) :
    1 ≤ 1+Real.log (α*scaleCutoff α u) ∧
      1+Real.log (α*scaleCutoff α u) ≤ 6*(1+Real.log u) := by
  have hα0 : 0 < α := by linarith
  have hN : 0 < scaleCutoff α u := hu.trans_le (scaleCutoff_bounds hα hu hαu).1
  have hNR : (1 : ℝ) ≤ scaleCutoff α u := by exact_mod_cast hN
  have hy : 1 ≤ α*scaleCutoff α u := one_le_mul_of_one_le_of_one_le hα hNR
  refine ⟨by linarith only [Real.log_nonneg hy], ?_⟩
  have hupper : α*scaleCutoff α u ≤ (u : ℝ)^6 := by
    have hh : (scaleCutoff α u : ℝ) ≤ (u : ℝ)^6/α := Nat.floor_le (by positivity)
    nlinarith only [(le_div_iff₀ hα0).mp hh]
  have hh := Real.log_le_log (show 0 < α*scaleCutoff α u by positivity) hupper
  rw [Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  linarith only [hh]

/-- A fixed logarithmic loss and a nonnegative row error transfer from u^6
to the actual main cutoff N=floor(u^6/α). -/
lemma scale_log_weight_tendsto {α : ℝ} (hα : 1 ≤ α) (k : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (f : ℕ → ℝ) (hf : ∀ u, 0 ≤ f u)
    (hlim : Tendsto (fun u : ℕ => (root64 u : ℝ)*(1+Real.log u)^k*f u/(u : ℝ)^6) atTop (𝓝 0)) :
    Tendsto (fun u : ℕ => C*(root64 u : ℝ)*(1+Real.log (α*scaleCutoff α u))^k*f u/
      (scaleCutoff α u : ℝ)) atTop (𝓝 0) := by
  have hα0 : 0 < α := by linarith
  have hh := hlim.const_mul (2*α*C*6^k)
  simp only [mul_zero] at hh
  apply squeeze_zero_norm' _ hh
  filter_upwards [eventually_ge_atTop (1 : ℕ), eventually_ge_atTop ⌈α⌉₊] with u hu huα
  have hαu : α ≤ u := (Nat.le_ceil α).trans (Nat.cast_le.mpr huα)
  have huR : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  obtain ⟨huN, _, hscale⟩ := scaleCutoff_bounds hα hu hαu
  have hNR : (0 : ℝ) < scaleCutoff α u := Nat.cast_pos.mpr (hu.trans huN)
  obtain ⟨hL, hlog⟩ := scale_log_bound hα hu hαu
  have hL0 : 0 ≤ 1+Real.log (α*scaleCutoff α u) := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity [hf u])]
  have hinv : 1/(scaleCutoff α u : ℝ) ≤ 2*α/(u : ℝ)^6 := by
    apply (div_le_div_iff₀ hNR (pow_pos huR 6)).mpr
    simpa only [one_mul] using hscale
  calc
    _ = (C*(root64 u : ℝ)*(1+Real.log (α*scaleCutoff α u))^k*f u)*(1/(scaleCutoff α u : ℝ)) := by ring
    _ ≤ (C*(root64 u : ℝ)*(6*(1+Real.log u))^k*f u)*(2*α/(u : ℝ)^6) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hL0 hlog k) (by positivity)) (hf u)
      · exact hinv
      · positivity
      · positivity [Real.log_natCast_nonneg u, hf u]
    _ = _ := by rw [mul_pow]; ring

lemma eventually_bound_of_scaled_limit {α : ℝ} (hα : 1 ≤ α) (f : ℕ → ℝ)
    (hlim : Tendsto (fun u => f u/(scaleCutoff α u : ℝ)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ u : ℕ in atTop, f u ≤ ε*(scaleCutoff α u : ℝ) := by
  filter_upwards [(tendsto_order.mp hlim).2 ε hε,
    (scaleCutoff_tendsto hα).eventually_ge_atTop 1] with u hu hN
  exact ((div_lt_iff₀ (Nat.cast_pos.mpr hN)).mp hu).le

lemma eventually_original_covariance_budget {α : ℝ} (hα : 1 ≤ α) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop,
      200*(root64 u : ℝ)*(1+Real.log (α*scaleCutoff α u))^3*(polynomialRowError u (root64 u)+1)+
        2*|commonLogCenter (α*scaleCutoff α u)|/α ≤ ε*(scaleCutoff α u : ℝ) := by
  have he := scale_log_weight_tendsto hα 3 (by norm_num : (0 : ℝ) ≤ 200)
    (fun u => polynomialRowError u (root64 u)+1)
    (by intro u; unfold polynomialRowError; positivity [Erdos972PrimeRotation.rotationConstant_pos 256, Real.log_natCast_nonneg u])
    (summed_polynomialRowError_add_one_tendsto 3)
  have hm := (common_log_main_div_tendsto (show 0 < α by linarith)).comp (scaleCutoff_tendsto hα)
  have hh := he.add hm
  simp only [Function.comp_apply, ← add_div, add_zero] at hh
  exact eventually_bound_of_scaled_limit hα _ hh hε

lemma eventually_dual_covariance_budget {α : ℝ} (hα : 1 ≤ α) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop,
      2*|covariance (scaleCutoff α u) (fun n => vonMangoldt n) (fun n => Real.log n)|+
        50*(root64 u : ℝ)*(1+Real.log (α*scaleCutoff α u))^3*
          (scaledRowError (dualScaleLoss α) u (root64 u)+118*(root64 u : ℝ)*(u : ℝ)^4+1) ≤
            ε*(scaleCutoff α u : ℝ) := by
  have he := scale_log_weight_tendsto hα 3 (by norm_num : (0 : ℝ) ≤ 50)
    (fun u => scaledRowError (dualScaleLoss α) u (root64 u))
    (by intro u; unfold scaledRowError; positivity [Erdos972PrimeRotation.rotationConstant_pos (256*dualScaleLoss α), Real.log_natCast_nonneg u])
    (summed_scaledRowError_tendsto (dualScaleLoss α) 3)
  have hm : Tendsto (fun u => 2*|covariance (scaleCutoff α u) (fun n => vonMangoldt n) (fun n => Real.log n)|/
      (scaleCutoff α u : ℝ)) atTop (𝓝 0) := by
    have hh := ((mangoldt_log_covariance_tendsto.comp (scaleCutoff_tendsto hα)).abs.const_mul 2)
    simp only [Function.comp_apply, abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), abs_zero, mul_zero] at hh
    simpa only [mul_div_assoc] using hh
  have hh := hm.add he
  simp only [← add_div, add_zero] at hh
  have hhalf := eventually_bound_of_scaled_limit hα _ hh (show 0 < ε/2 by positivity)
  filter_upwards [hhalf, eventually_covariance_budget hα (show 0 < ε/2 by positivity),
    eventually_ge_atTop (1 : ℕ), eventually_ge_atTop ⌈α⌉₊] with u hhalf hbudget hu huα
  have hαu : α ≤ u := (Nat.le_ceil α).trans (Nat.cast_le.mpr huα)
  have hL := (scale_log_bound hα hu hαu).1
  have hv : (1 : ℝ) ≤ root64 u := by exact_mod_cast (root64_bounds hu).1
  let L := 1+Real.log (α*scaleCutoff α u)
  let B := 118*(root64 u : ℝ)*(u : ℝ)^4
  have hB : 0 ≤ B+1 := by dsimp [B]; positivity
  have hpower : (root64 u : ℝ)*L^3 ≤ (root64 u : ℝ)^2*L^5 := by
    have hv2 : (root64 u : ℝ) ≤ (root64 u : ℝ)^2 := by nlinarith only [hv]
    exact mul_le_mul hv2 (pow_le_pow_right₀ hL (by norm_num)) (by positivity [hL]) (sq_nonneg _)
  have hminor : 50*(root64 u : ℝ)*L^3*(B+1) ≤ 100*(B+1)*(root64 u : ℝ)^2*L^5 := by
    have hh := mul_le_mul_of_nonneg_left hpower (show 0 ≤ 50*(B+1) by positivity)
    have hp : 0 ≤ (B+1)*(root64 u : ℝ)^2*L^5 := by positivity [hL]
    nlinarith only [hh, hp]
  dsimp only [L, B] at hminor
  nlinarith only [hhalf, hbudget, hminor]

lemma eventually_double_typeI_budget {α : ℝ} (hα : 1 ≤ α) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop,
      32*(scaleCutoff α u : ℝ)*|reciprocalMoebius (growingCutoff u)*reciprocalMoebius (growingCutoff u)|+
        100*(118*(root64 u : ℝ)*(u : ℝ)^4+1)*(root64 u : ℝ)^2*
          (1+Real.log (α*scaleCutoff α u))^5 ≤ ε*(scaleCutoff α u : ℝ) := by
  filter_upwards [eventually_covariance_budget hα (show 0 < ε/2 by positivity),
    (tendsto_order.mp growing_slope_product_tendsto).2 (ε/2) (by positivity)] with u he hm
  have hh := mul_le_mul_of_nonneg_right hm.le (Nat.cast_nonneg (α := ℝ) (scaleCutoff α u))
  nlinarith only [he, hh]

#print axioms eventually_original_covariance_budget
#print axioms eventually_dual_covariance_budget
#print axioms eventually_double_typeI_budget

end Erdos972CovarianceScaleBudgets
