import Submission.DualProfileCovariance
import Submission.TypeICovariance

/-! The dual Type-I covariance, with both the actual output logarithm and
the isolated Mangoldt cutoff restored. -/
namespace Erdos972DualTypeICovariance

open Finset ArithmeticFunction
open Erdos972DualProfileCovariance Erdos972TypeICovariance Erdos972TypeIPolynomial
open Erdos972LogarithmicCovariance Erdos972LogDivisorProfiles Erdos972ProfileLogShift
open Erdos972CovariancePerturbation Erdos972DualPrimeRows Erdos972DivisorCovariance
open Erdos972PrimePowerError Erdos972DivisorPairCount Erdos972Vaughan Erdos972DoubleVaughan
open Erdos972TypeISmallBounds Erdos972ChebyshevRowMean Erdos972MobiusPartialSums

set_option maxHeartbeats 1000000

/-- A fully restored dual Type-I bound. Its only common main term is
sublinear by qualitative PNT; the remaining errors are quantitative. -/
theorem dual_typeI_covariance_bound {α : ℝ} (hα : 1 ≤ α) {N S T v : ℕ}
    (hS : 0 < S) (hT : 0 < T) (hEv : S*T ≤ v) (hvN : v ≤ N)
    {Bp Bd : ℝ} (hBp : 0 ≤ Bp) (hBd : 0 ≤ Bd)
    (hrows : ∀ j ≤ N, ∀ e ∈ Ioc 0 (S*T), |inputDivisorRow α e j-Chebyshev.psi j/e| ≤ Bp)
    (hlocal : ∀ j ≤ N, ∀ a ∈ Ioc 0 1, ∀ b ∈ Ioc 0 (S*T),
      |((divisorPairs α j a b).card : ℝ)-(j : ℝ)/(a*b)| ≤ Bd) :
    |covariance N (fun n => vonMangoldt n) (fun n => typeIPart S T (floorMul α n))| ≤
      2*|covariance N (fun n => vonMangoldt n) (fun n => Real.log n)|+
        50*(v : ℝ)*(1+Real.log (α*N))^3*(Bp+Bd+1) := by
  have hE : 0 < S*T := Nat.mul_pos hS hT
  have hv : 0 < v := hE.trans_le hEv
  have hN : 0 < N := hv.trans_le hvN
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hα0 : 0 < α := by linarith
  have hαN : (N : ℝ) ≤ α*N := le_mul_of_one_le_left hNR.le hα
  have hαN1 : 1 ≤ α*N := (by exact_mod_cast hN : (1 : ℝ) ≤ N).trans hαN
  let L : ℝ := 1+Real.log (α*N)
  have hL : 1 ≤ L := by dsimp only [L]; linarith [Real.log_nonneg hαN1]
  have hL0 : 0 ≤ L := by linarith
  have hlogN : Real.log N ≤ L-1 := by
    dsimp only [L]
    linarith only [Real.log_le_log hNR hαN]
  have hlogα : Real.log α ≤ L-1 := by
    have hh : α ≤ α*N := le_mul_of_one_le_right hα0.le (by exact_mod_cast hN)
    dsimp only [L]
    linarith only [Real.log_le_log hα0 hh]
  have hlogE : Real.log (S*T : ℕ) ≤ L-1 :=
    (Erdos972ExponentialSum.monotone_log_natCast (hEv.trans hvN)).trans hlogN
  have hM := typeI_profileMass_le hEv hL hlogE
  have hcm : coefficientMass (S*T) (slopeCoeff S) ≤ (v : ℝ) :=
    (slopeCoeff_mass S (S*T)).trans (Nat.cast_le.mpr hEv)
  let G := alignedOutput α (S*T) (slopeCoeff S)
    (fun k => Real.log α*slopeCoeff S k+constantCoeff S T k)
  have hshift : profileMass (S*T) (slopeCoeff S)
      (fun k => Real.log α*slopeCoeff S k+constantCoeff S T k) ≤ 2*(v : ℝ)*L^2 := by
    have hs := profileMass_shift (S*T) (Real.log α) (slopeCoeff S) (constantCoeff S T)
    rw [abs_of_nonneg (Real.log_nonneg hα)] at hs
    have hh := mul_le_mul (show 1+Real.log α ≤ L by linarith only [hlogα]) hM
      (profileMass_nonneg _ _ _) hL0
    exact hs.trans (hh.trans_eq (by ring))
  have hbody := prime_aligned_covariance α hN (by norm_num : 0 < 1) (slopeCoeff S)
    (fun k => Real.log α*slopeCoeff S k+constantCoeff S T k) hBp hBd hrows hlocal
  rw [slopeCoeff_mean (show S ≤ S*T by nlinarith)] at hbody
  have hmain := mul_le_mul_of_nonneg_right (reciprocalMoebius_bound S)
    (abs_nonneg (covariance N (fun n => vonMangoldt n) (fun n => Real.log n)))
  have herr : 2*(1+Real.log N)*(Bp+7*Bd)*profileMass (S*T) (slopeCoeff S)
      (fun k => Real.log α*slopeCoeff S k+constantCoeff S T k) ≤
        4*(v : ℝ)*L^3*(Bp+7*Bd) := by
    have hh := mul_le_mul (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (show 1+Real.log N ≤ L by linarith only [hlogN])
        (by norm_num : (0 : ℝ) ≤ 2)) (show 0 ≤ Bp+7*Bd by positivity)) hshift
      (profileMass_nonneg _ _ _) (by positivity)
    exact hh.trans_eq (by ring)
  have hl1 : total N (fun n => |typeIPart S T (floorMul α n)-G n|) ≤ 8*(v : ℝ)*L := by
    have he : total N (fun n => |typeIPart S T (floorMul α n)-G n|) ≤
        total N (fun n => |profile (S*T) (slopeCoeff S) (constantCoeff S T) (floorMul α n)-G n|)+
          ∑ n ∈ Ioc 0 N, cutoff Λ T (floorMul α n) := by
      simp only [total, ← sum_add_distrib]
      apply sum_le_sum
      intro n hn
      rw [typeIPart_profile S T hT (floorMul_pos hα (mem_Ioc.mp hn).1)]
      have hid (a b c : ℝ) : a+b-c = (a-c)+b := by ring
      rw [hid]
      exact (abs_add_le _ _).trans_eq (by rw [abs_of_nonneg (cutoff_vonMangoldt_nonneg _ _)])
    have hlog := profile_log_shift_l1 hα N (S*T) (slopeCoeff S) (constantCoeff S T)
    have hlog' := mul_le_mul hcm (show 1+Real.log N ≤ L by linarith only [hlogN])
      (by linarith [Real.log_natCast_nonneg N]) (Nat.cast_nonneg (α := ℝ) v)
    have hsmall := (cutoff_mangoldt_output_sum_le hα T N).trans (psi_le_seven_mul (Nat.cast_nonneg T))
    have hTv : (T : ℝ) ≤ v := Nat.cast_le.mpr ((show T ≤ S*T by nlinarith).trans hEv)
    have hh := mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg (α := ℝ) v)
    change total N (fun n => |profile (S*T) (slopeCoeff S) (constantCoeff S T) (floorMul α n)-G n|) ≤ _ at hlog
    nlinarith only [he, hlog, hlog', hsmall, hTv, hh]
  have hf : ∀ n ∈ Ioc 0 N, |vonMangoldt n| ≤ L := by
    intro n hn
    rw [abs_of_nonneg vonMangoldt_nonneg]
    exact vonMangoldt_le_log.trans ((log_input_le hn).trans (hlogN.trans (by linarith)))
  have hp := covariance_second_perturb hN (fun n => vonMangoldt n)
    (fun n => typeIPart S T (floorMul α n)) G hf
  have hpert : |covariance N (fun n => vonMangoldt n) (fun n => typeIPart S T (floorMul α n))-
      covariance N (fun n => vonMangoldt n) G| ≤ 16*(v : ℝ)*L^2 := by
    have hh := mul_le_mul_of_nonneg_left hl1 (show 0 ≤ 2*L by positivity)
    nlinarith only [hp, hh]
  have hrest : 4*(v : ℝ)*L^3*(Bp+7*Bd)+16*(v : ℝ)*L^2 ≤
      50*(v : ℝ)*L^3*(Bp+Bd+1) := by
    have hp := pow_le_pow_right₀ hL (by norm_num : 2 ≤ 3)
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ 16*(v : ℝ) by positivity)
    nlinarith only [hh, show 0 ≤ (v : ℝ)*L^3*Bp by positivity,
      show 0 ≤ (v : ℝ)*L^3*Bd by positivity, show 0 ≤ (v : ℝ)*L^3 by positivity]
  have ht := abs_sub_le (covariance N (fun n => vonMangoldt n) (fun n => typeIPart S T (floorMul α n)))
    (covariance N (fun n => vonMangoldt n) G) 0
  simp only [sub_zero] at ht
  change |covariance N (fun n => vonMangoldt n) G| ≤ _ at hbody
  change _ ≤ 2*|covariance N (fun n => vonMangoldt n) (fun n => Real.log n)|+50*(v : ℝ)*L^3*(Bp+Bd+1)
  nlinarith only [hbody, hmain, herr, hpert, hrest, ht]

#print axioms dual_typeI_covariance_bound

end Erdos972DualTypeICovariance
