import Submission.RemainderMeanProductError

/-! Prime-power removal for the actual centered covariance, including the
change in both means. This is an error estimate, not a correlation lower bound. -/
namespace Erdos972CenteredPrimeFactorError
open Finset
open Erdos972DoubleVaughan Erdos972PrimeFactorRemainder Erdos972PrimePowerError
open Erdos972LogarithmicCovariance Erdos972CenteredDoubleVaughan
open Erdos972UniformPrimeFactorError Erdos972PrimeFactorError
open Erdos972RemainderMeanProductError Erdos972MeanProductErrorAlgebra
set_option maxHeartbeats 1200000
set_option autoImplicit false

noncomputable def centeredPrimeRemainder (α : ℝ) (N U V : ℕ) : ℝ :=
  covariance N (primeTypeIIPart U V) (fun n => primeTypeIIPart U V (floorMul α n))

noncomputable def centeredPrimeFactorError (α : ℝ) (N U V : ℕ) : ℝ :=
  centeredFourFactor α N U V U V - centeredPrimeRemainder α N U V

lemma centered_error_identity (α : ℝ) (N U V : ℕ) :
    centeredPrimeFactorError α N U V/(N : ℝ) =
      primeFactorError α N U V/(N : ℝ)-meanProductError α N U V := by
  unfold centeredPrimeFactorError centeredFourFactor centeredPrimeRemainder
    covariance primeFactorError pairSum meanProductError total
  ring

lemma centered_error_normalized_fourth {α L : ℝ} (hα : 1 ≤ α) {N U V Z : ℕ}
    (hN : 0 < N) (hZ : 0 < Z) (hV : Z^3 ≤ V)
    (hiL : 1+Real.log N ≤ L) (hoL : 1+Real.log (floorMul α N) ≤ L) :
    |centeredPrimeFactorError α N U V/(N : ℝ)|^4 ≤
      4096*α^4*L^38/(Z : ℝ)^2 := by
  have hL : 1 ≤ L := by linarith [Real.log_natCast_nonneg N]
  have hL0 : 0 ≤ L := by linarith
  have hα0 : 0 ≤ α := by linarith
  have hraw := primeFactorError_normalized_fourth_general (U := U) hα hN hZ hV hiL hoL
  have hmean := meanProductError_fourth_bound (U := U) hα hN hZ hV hiL hoL
  have hsum : (1+α)^2 ≤ 4*α^2 := by nlinarith only [hα]
  have hα34 : α^3 ≤ α^4 := pow_le_pow_right₀ hα (by norm_num)
  have hcoeff : 16*α*(1+α)^2 ≤ 64*α^4 := by
    calc
      _ ≤ 16*α*(4*α^2) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 64*α^3 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hα34 (by norm_num)
  have hraw' : |primeFactorError α N U V/(N : ℝ)|^4 ≤ 64*α^4*L^38/(Z : ℝ)^2 := by
    apply hraw.trans
    gcongr
  have hLpow : L^20 ≤ L^38 := pow_le_pow_right₀ hL (by norm_num)
  have hmean' : |meanProductError α N U V|^4 ≤ 256*α^4*L^38/(Z : ℝ)^2 := by
    apply hmean.trans
    gcongr
  rw [centered_error_identity]
  apply (fourth_sub_le _ _).trans
  calc
    _ ≤ 8*(64*α^4*L^38/(Z : ℝ)^2+256*α^4*L^38/(Z : ℝ)^2) := by gcongr
    _ = 2560*(α^4*L^38/(Z : ℝ)^2) := by ring
    _ ≤ 4096*(α^4*L^38/(Z : ℝ)^2) := by gcongr <;> norm_num
    _ = _ := by ring

#print axioms centered_error_identity
#print axioms centered_error_normalized_fourth
end Erdos972CenteredPrimeFactorError
