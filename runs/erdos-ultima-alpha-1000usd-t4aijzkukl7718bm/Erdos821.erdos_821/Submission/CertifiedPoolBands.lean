import Submission.PoolBandBounds

/-!
# Integer certificates for retained-pool rejection bands

These certify the existing band majorant. They do not change its distribution
level or prove arbitrary-root smooth-prime supply.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

/-- Numerator of a rational upper bound for one limiting band cost. -/
def poolBandNumerator (u v b : ℕ) : ℕ :=
  40000021*(200000000*1025^2*500000+b*1024^2)*(v-u)

def poolBandDenominator (u v b : ℕ) : ℕ :=
  2*b*1024^2*500000*u*v

lemma poolBandDenominator_pos (u v b : ℕ) (hu : 0 < u) (hv : 0 < v) (hb : 0 < b) :
    0 < poolBandDenominator u v b := by
  unfold poolBandDenominator
  positivity

lemma poolBandLimit_le_rational (u v b : ℕ) (hu : 0 < u) (huv : u ≤ v) (hb : 0 < b) :
    scaledProductLongLimit (poolBandCoefficient b) u v ≤
      (poolBandNumerator u v b : ℝ)/(poolBandDenominator u v b : ℝ) := by
  have hv : 0 < v := hu.trans_le huv
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hΔ : 0 ≤ 1/(128*(u : ℝ))-1/(128*(v : ℝ)) := by
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast huv) (by norm_num)
  unfold scaledProductLongLimit
  apply (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (add_le_add_right productSupply_log_error_coefficient (poolBandCoefficient b))
      (by norm_num : (0 : ℝ) ≤ 64*40000021)) hΔ).trans_eq
  unfold poolBandCoefficient poolBandNumerator poolBandDenominator
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub huv]
  push_cast
  field_simp [huR.ne',hvR.ne',hbR.ne']
  ring

/-- Upward rounding is strict even if the rational cost is an integer. -/
def poolBandCertificate (D u v b : ℕ) : ℕ :=
  (poolBandNumerator u v b*D)/poolBandDenominator u v b+1

lemma poolBandLimit_lt_certificate (D u v b : ℕ) (hD : 0 < D)
    (hu : 0 < u) (huv : u ≤ v) (hb : 0 < b) :
    scaledProductLongLimit (poolBandCoefficient b) u v <
      (poolBandCertificate D u v b : ℝ)/(D : ℝ) := by
  have hv := hu.trans_le huv
  have hden := poolBandDenominator_pos u v b hu hv hb
  have hmod := Nat.mod_lt (poolBandNumerator u v b*D) hden
  have hdecomp := Nat.mod_add_div (poolBandNumerator u v b*D) (poolBandDenominator u v b)
  have hn : poolBandNumerator u v b*D <
      poolBandCertificate D u v b*poolBandDenominator u v b := by
    unfold poolBandCertificate
    nlinarith only [hmod,hdecomp]
  apply (poolBandLimit_le_rational u v b hu huv hb).trans_lt
  apply (div_lt_div_iff₀ (by exact_mod_cast hden : (0 : ℝ) < poolBandDenominator u v b)
    (by exact_mod_cast hD : (0 : ℝ) < D)).mpr
  exact_mod_cast hn

end Erdos821.AnalyticSieve
