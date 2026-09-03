import Submission.WideMetricSieve
import Submission.WidePairWeights

/-! Uniform weighted upper sieve bounds on arbitrary fixed slope ranges. -/
namespace Erdos972WideSieveBound

open Erdos972WideMetricSieve Erdos972WidePairWeights Erdos972PairSieve
open Erdos972ChebyshevLower Erdos972RichSlopes

set_option maxHeartbeats 1000000

lemma primeInputs_power_upper (A : ℕ) {α : ℝ} (hα : 1 < α) (hα9 : α < (A : ℝ) + 1)
    {v : ℕ} (hv : 2 ≤ v) (hbad : α ∉ wideBadSlopes A (v^24) (v^28)) :
    ((primeInputs α (v^40)).card : ℝ) ≤
      4 * (v : ℝ)^40 / (Real.log (v + 1))^2 + 16 * (v : ℝ)^38 := by
  have hv0 : (0 : ℝ) < v := Nat.cast_pos.mpr (by omega)
  have hv1 : (1 : ℝ) ≤ v := by exact_mod_cast (show 1 ≤ v by omega)
  have hv2 : (2 : ℝ) ≤ v := by exact_mod_cast hv
  have hvN1 : 1 ≤ v := by omega
  obtain ⟨r, hr0, hrlo, hrhi, hrerr⟩ :=
    exists_approximant_of_not_mem_wideBadSlopes A hα hα9 (v^24) (v^28) (by positivity) hbad
  have hq : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
  have hqlo : (v : ℝ)^24 ≤ r.den := by exact_mod_cast hrlo.le
  have hqhi : (r.den : ℝ) ≤ (v : ℝ)^28 := by exact_mod_cast hrhi
  have hδ : |α - r| ≤ 1 / (v : ℝ)^52 := by
    apply hrerr.trans
    push_cast
    apply one_div_le_one_div_of_le (by positivity)
    calc
      (v : ℝ)^52 = (v : ℝ)^28 * (v : ℝ)^24 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hqlo (by positivity)
  have hsmall : 2 * (v^40 : ℕ) * |α - r| ≤ (1 : ℝ) := by
    push_cast
    calc
      _ ≤ 2 * (v : ℝ)^40 * (1 / (v : ℝ)^52) := by gcongr
      _ = 2 / (v : ℝ)^12 := by field_simp
      _ ≤ 1 := (div_le_one (by positivity)).mpr
        (hv2.trans (by simpa using pow_le_pow_right₀ hv1 (show 1 ≤ 12 by omega)))
  have hRN : v^2 ≤ v^40 := Nat.pow_le_pow_right hvN1 (by omega)
  have hc := primeInputs_rational_upper hα.le r hr0 (v^40) v hvN1 hRN hsmall
  push_cast at hc
  have h₁ : 8 * ((v : ℝ)^40)^2 * |α - r| ≤ 8 * (v : ℝ)^28 := by
    calc
      _ ≤ 8 * ((v : ℝ)^40)^2 * (1 / (v : ℝ)^52) := by gcongr
      _ = _ := by field_simp
  have h₂ : 2 * (v : ℝ)^40 / r.den ≤ 2 * (v : ℝ)^16 := by
    calc
      _ ≤ 2 * (v : ℝ)^40 / (v : ℝ)^24 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hqlo
      _ = _ := by field_simp
  have h₃ : 3 * (v : ℝ)^2 * r.den ≤ 3 * (v : ℝ)^30 := by
    calc
      _ ≤ 3 * (v : ℝ)^2 * (v : ℝ)^28 := by gcongr
      _ = _ := by ring
  have hp28 : (v : ℝ)^28 ≤ (v : ℝ)^30 := pow_le_pow_right₀ hv1 (by omega)
  have hp16 : (v : ℝ)^16 ≤ (v : ℝ)^30 := pow_le_pow_right₀ hv1 (by omega)
  have hp0 : (1 : ℝ) ≤ (v : ℝ)^30 := one_le_pow₀ hv1
  have hB : 8 * ((v : ℝ)^40)^2 * |α - r| + 2 * (v : ℝ)^40 / r.den +
      3 * (v : ℝ)^2 * r.den + 2 ≤ 15 * (v : ℝ)^30 := by linarith
  have hBm := mul_le_mul_of_nonneg_right hB (show 0 ≤ (v : ℝ)^8 by positivity)
  have hv38 : (v : ℝ) ≤ (v : ℝ)^38 := by
    simpa using pow_le_pow_right₀ hv1 (show 1 ≤ 38 by omega)
  have heq : 15 * (v : ℝ)^30 * (v : ℝ)^8 = 15 * (v : ℝ)^38 := by ring
  rw [heq] at hBm
  linarith

/-- The weighted first moments cannot concentrate outside these small rational
neighborhoods at a rate larger than a fixed multiple of the input cutoff. -/
theorem widePairs_power_upper (A : ℕ) (hA : 1 ≤ A) {α : ℝ} (hα : 1 < α) (hα9 : α < (A : ℝ) + 1)
    {v : ℕ} (hv : 2 ≤ v) (hAv : A ≤ v) (hbad : α ∉ wideBadSlopes A (v^24) (v^28)) :
    widePairs A (v^40) α ≤ 40000 * (v : ℝ)^40 := by
  have hAPos : (0 : ℝ) < A := Nat.cast_pos.mpr (by omega)
  have hA1R : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hAvR : (A : ℝ) ≤ v := Nat.cast_le.mpr hAv
  have hv0 : (0 : ℝ) < v := Nat.cast_pos.mpr (by omega)
  have hv2 : (2 : ℝ) ≤ v := by exact_mod_cast hv
  have hv1 : (1 : ℝ) ≤ v := by linarith
  have hvN1 : 1 ≤ v := by omega
  have hN2 : 2 ≤ v^40 := hv.trans (by simpa using Nat.pow_le_pow_right hvN1 (show 1 ≤ 40 by omega))
  have hcard := primeInputs_power_upper A hα hα9 hv hbad
  have hw := widePairs_le_card A hA hN2 α
  change widePairs A (v^40) α ≤ (primeInputs α (v^40)).card *
    (Real.log (v^40 : ℕ) * Real.log ((A : ℝ) * (v^40 : ℕ))) at hw
  push_cast at hw
  have hlog : 0 ≤ Real.log v := Real.log_nonneg hv1
  have hlognext : 0 < Real.log (v + 1) := Real.log_pos (by linarith)
  have hlogmono : Real.log v ≤ Real.log (v + 1) := Real.log_le_log hv0 (by linarith)
  have hlogv : Real.log v ≤ (v : ℝ) := by linarith [Real.log_le_sub_one_of_pos hv0]
  have hlog8 : Real.log A ≤ 3 * Real.log v := by
    have h := Real.log_le_log hAPos hAvR
    linarith
  have hprod : Real.log ((v : ℝ)^40) * Real.log ((A : ℝ) * (v : ℝ)^40) ≤
      1720 * (Real.log v)^2 := by
    rw [Real.log_mul hAPos.ne' (pow_ne_zero _ hv0.ne'), Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hprodn : 0 ≤ Real.log ((v : ℝ)^40) * Real.log ((A : ℝ) * (v : ℝ)^40) := by
    apply mul_nonneg <;> apply Real.log_nonneg
    · exact one_le_pow₀ hv1
    · nlinarith [one_le_pow₀ (n := 40) hv1]
  have hA0 : 0 ≤ 4 * (v : ℝ)^40 / (Real.log (v + 1))^2 + 16 * (v : ℝ)^38 := by positivity
  have hh := mul_le_mul hcard hprod hprodn hA0
  have hb := hw.trans hh
  have hratio : (Real.log v)^2 / (Real.log (v + 1))^2 ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos hlognext)).mpr
    nlinarith
  have hmain : (4 * (v : ℝ)^40 / (Real.log (v + 1))^2) * (1720 * (Real.log v)^2) ≤
      6880 * (v : ℝ)^40 := by
    calc
      _ = (6880 * (v : ℝ)^40) * ((Real.log v)^2 / (Real.log (v + 1))^2) := by ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hratio
  have hsquare : (Real.log v)^2 ≤ (v : ℝ)^2 := by nlinarith
  have herror : (16 * (v : ℝ)^38) * (1720 * (Real.log v)^2) ≤ 27520 * (v : ℝ)^40 := by
    calc
      _ ≤ (16 * (v : ℝ)^38) * (1720 * (v : ℝ)^2) := by gcongr
      _ = _ := by ring
  nlinarith


#print axioms widePairs_power_upper
end Erdos972WideSieveBound
