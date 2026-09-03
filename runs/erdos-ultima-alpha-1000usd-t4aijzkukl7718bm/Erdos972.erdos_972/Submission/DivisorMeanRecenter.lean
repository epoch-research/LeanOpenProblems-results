import Submission.CenteredLowMellinBlock
import Submission.CenteredDoubleVaughan

/-! Exact accounting for centering the divisor coefficient in Vaughan's
remainder. The resulting covariance correction is retained, not set to zero. -/
namespace Erdos972DivisorMeanRecenter

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Erdos972Vaughan Erdos972DoubleVaughan Erdos972CenteredDoubleVaughan
open Erdos972MellinDivisorCoefficient Erdos972MobiusPartialSums
open Erdos972PrimePowerError Erdos972LogarithmicCovariance
open Erdos972CenteredLowMellinBlock

set_option autoImplicit false
set_option maxHeartbeats 1500000

noncomputable def pointScale (c : ℝ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => c*f n, by simp⟩

@[simp] lemma pointScale_apply (c : ℝ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    pointScale c f n = c*f n := rfl

lemma pointScale_mul (c : ℝ) (f g : ArithmeticFunction ℝ) :
    pointScale c f*g = pointScale c (f*g) := by
  ext n
  simp only [ArithmeticFunction.mul_apply, pointScale_apply, mul_sum, mul_assoc]

noncomputable def meanCenteredDivisorCoeff (U : ℕ) : ArithmeticFunction ℝ :=
  tail (μ : ArithmeticFunction ℝ) U*ζ+pointScale (reciprocalMoebius U) ζ

lemma meanCenteredDivisorCoeff_apply {n : ℕ} (hn : n ≠ 0) (U : ℕ) :
    meanCenteredDivisorCoeff U n = divisorCoeff U n+reciprocalMoebius U := by
  simp only [meanCenteredDivisorCoeff, ArithmeticFunction.add_apply, pointScale_apply,
    natCoe_apply, zeta_apply_ne hn, Nat.cast_one, mul_one, divisorCoeff]

noncomputable def logTail (V : ℕ) : ArithmeticFunction ℝ := ζ*tail vonMangoldt V

lemma logTail_eq (V : ℕ) :
    logTail V = ArithmeticFunction.log-ζ*cutoff vonMangoldt V := by
  rw [logTail, tail, mul_sub, zeta_mul_vonMangoldt]

lemma cutoff_moebius_one : cutoff (μ : ArithmeticFunction ℝ) 1 = 1 := by
  ext n
  by_cases hn0 : n = 0
  · simp [hn0]
  by_cases hn1 : n = 1
  · simp [hn1, cutoff, one_apply]
  have hn : ¬n ≤ 1 := by omega
  simp [cutoff, hn, hn1]

/-- The correction has a Type-I expression plus its explicit small term. -/
lemma logTail_typeI (V : ℕ) : logTail V = typeIPart 1 V-cutoff vonMangoldt V := by
  rw [logTail_eq, typeIPart, cutoff_moebius_one, one_mul, one_mul]
  abel

noncomputable def meanCenteredTypeII (U V : ℕ) : ArithmeticFunction ℝ :=
  meanCenteredDivisorCoeff U*tail vonMangoldt V

lemma meanCenteredTypeII_eq (U V : ℕ) :
    meanCenteredTypeII U V = typeIIPart U V+pointScale (reciprocalMoebius U) (logTail V) := by
  rw [meanCenteredTypeII, meanCenteredDivisorCoeff, add_mul, pointScale_mul]
  rfl

noncomputable def meanCenteredTypeI (U V : ℕ) : ArithmeticFunction ℝ :=
  typeIPart U V-pointScale (reciprocalMoebius U) (logTail V)

/-- This is an exact replacement decomposition, not a dropped mean term. -/
theorem mean_centered_vaughan_identity (U V : ℕ) :
    vonMangoldt = meanCenteredTypeI U V+meanCenteredTypeII U V := by
  rw [meanCenteredTypeI, meanCenteredTypeII_eq]
  have hh := mangoldt_split U V
  rw [hh]
  abel

lemma centeredBlock_arithmetic (U M : ℕ) (t : ℝ) :
    centeredBlock U M t =
      ∑ n ∈ Ioc M (2*M), mellinPhase t n*(meanCenteredDivisorCoeff U n : ℂ) := by
  unfold centeredBlock
  apply sum_congr rfl
  intro n hn
  rw [meanCenteredDivisorCoeff_apply (Nat.ne_of_gt ((Nat.zero_le M).trans_lt (mem_Ioc.mp hn).1))]

lemma covariance_scale_left (N : ℕ) (f g : ℕ → ℝ) (a : ℝ) :
    covariance N (fun n => a*f n) g = a*covariance N f g := by
  simp only [covariance, total, mul_assoc, ← mul_sum]
  ring

lemma covariance_scale_right (N : ℕ) (f g : ℕ → ℝ) (a : ℝ) :
    covariance N f (fun n => a*g n) = a*covariance N f g := by
  rw [Erdos972CovariancePerturbation.covariance_comm,
    covariance_scale_left, Erdos972CovariancePerturbation.covariance_comm N g f]

lemma covariance_linear_expand (N : ℕ) (f g h j : ℕ → ℝ) (a b : ℝ) :
    covariance N (fun n => f n+a*g n) (fun n => h n+b*j n) =
      covariance N f h+a*covariance N g h+b*covariance N f j+
        (a*b)*covariance N g j := by
  simp only [covariance_add_left, covariance_add_right, covariance_scale_left,
    covariance_scale_right]
  ring

noncomputable def meanCenteredFourFactor (α : ℝ) (N U V S T : ℕ) : ℝ :=
  covariance N (fun n => meanCenteredTypeII U V n)
    (fun n => meanCenteredTypeII S T (floorMul α n))

/-- Full actual covariance correction, including the mixed and quadratic
mean terms. No estimate of these terms is asserted by this identity. -/
theorem mean_centered_fourFactor_identity (α : ℝ) (N U V S T : ℕ) :
    meanCenteredFourFactor α N U V S T = centeredFourFactor α N U V S T+
      reciprocalMoebius U*covariance N (fun n => logTail V n)
        (fun n => typeIIPart S T (floorMul α n))+
      reciprocalMoebius S*covariance N (fun n => typeIIPart U V n)
        (fun n => logTail T (floorMul α n))+
      (reciprocalMoebius U*reciprocalMoebius S)*covariance N (fun n => logTail V n)
        (fun n => logTail T (floorMul α n)) := by
  unfold meanCenteredFourFactor centeredFourFactor
  simp only [meanCenteredTypeII_eq, ArithmeticFunction.add_apply, pointScale_apply]
  exact covariance_linear_expand N _ _ _ _ _ _

#print axioms logTail_typeI
#print axioms mean_centered_vaughan_identity
#print axioms centeredBlock_arithmetic
#print axioms mean_centered_fourFactor_identity
end Erdos972DivisorMeanRecenter
