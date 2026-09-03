import Submission.PoolBandBounds
import Submission.PoolBandBudgetAudit

/-!
# Linking the band-budget audit to the actual analytic coefficients

These are lower bounds for the certified rejection MAJORANT. They make
no assertion that the actual rejected-prime count is large.
-/
open Nat Finset
open scoped Classical BigOperators
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

lemma poolBandCoefficient_level_lower (b v : ℕ) (hb : 1 ≤ b)
    (hlevel : b*v < 100000000*10000000) :
    4*(v : ℝ) ≤ (40000021/2 : ℝ)*poolBandCoefficient b := by
  have hbR : (0 : ℝ)<b := by exact_mod_cast hb
  have hv : (b : ℝ)*v < 100000000*10000000 := by exact_mod_cast hlevel
  have hbase : 4*(v : ℝ) ≤ (40000021/2 : ℝ)*(200000000/(b : ℝ)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hbR).mpr
    norm_num at hv ⊢
    nlinarith only [hv]
  have hfactor : (1 : ℝ) ≤ (1+1/(2 : ℝ)^10)^2 := by norm_num
  have h := mul_le_mul_of_nonneg_left hfactor
    (show 0 ≤ (40000021/2 : ℝ)*(200000000/(b : ℝ)) by positivity)
  apply hbase.trans
  convert h using 1 <;> dsimp [poolBandCoefficient] <;> ring

/-- The actual scaled band limit dominates four times its logarithmic
endpoint increment under the multiplier-support level condition. -/
lemma scaled_pool_band_limit_ge_log (u v b : ℕ) (hu : 1 ≤ u) (huv : u ≤ v)
    (hb : 1 ≤ b) (hlevel : b*v < 100000000*10000000) :
    4*Real.log ((v : ℝ)/(u : ℝ)) ≤ scaledProductLongLimit (poolBandCoefficient b) u v := by
  have huR : (0 : ℝ)<u := by exact_mod_cast hu
  have huvR : (u : ℝ) ≤ v := by exact_mod_cast huv
  have hvR := huR.trans_le huvR
  have hΔ : 0 ≤ 1/(u : ℝ)-1/(v : ℝ) := sub_nonneg.mpr (one_div_le_one_div_of_le huR huvR)
  have hcoef := poolBandCoefficient_level_lower b v hb hlevel
  have h := log_ratio_le_band_budget (u : ℝ) (v : ℝ) (1/4)
    ((40000021/2 : ℝ)*poolBandCoefficient b) huR huvR (by norm_num)
    (by convert hcoef using 1; ring)
  have he : 0 ≤ (1/1000000 : ℝ)/Real.log 2 := by
    exact div_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
  have hextra : 0 ≤ (40000021/2 : ℝ)*((1/1000000 : ℝ)/Real.log 2)*(1/(u : ℝ)-1/(v : ℝ)) := by positivity
  have hraw : 4*Real.log ((v : ℝ)/(u : ℝ)) ≤
      ((40000021/2 : ℝ)*poolBandCoefficient b)*(1/(u : ℝ)-1/(v : ℝ)) := by
    convert h using 1; ring
  have hsum := le_add_of_nonneg_right (a := ((40000021/2 : ℝ)*poolBandCoefficient b)*(1/(u : ℝ)-1/(v : ℝ))) hextra
  apply hraw.trans
  apply hsum.trans_eq
  unfold scaledProductLongLimit
  simp only [div_mul_eq_div_div]
  ring

end Erdos821.AnalyticSieve
