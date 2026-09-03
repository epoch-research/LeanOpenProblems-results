import Submission.CommonCovarianceScales

/-! Exact centered second-factor decomposition. No sign is asserted for the
centered four-factor remainder. -/
namespace Erdos972CenteredDoubleVaughan

open Finset ArithmeticFunction
open Erdos972LogarithmicCovariance Erdos972DoubleVaughan Erdos972PrimePowerError

lemma covariance_add_left (N : ℕ) (f g h : ℕ → ℝ) :
    covariance N (fun n => f n+g n) h = covariance N f h+covariance N g h := by
  simp only [covariance, total, add_mul, sum_add_distrib]
  ring

lemma covariance_add_right (N : ℕ) (f g h : ℕ → ℝ) :
    covariance N f (fun n => g n+h n) = covariance N f g+covariance N f h := by
  simp only [covariance, total, mul_add, sum_add_distrib]
  ring

lemma covariance_double_split (N : ℕ) (A R B S : ℕ → ℝ) :
    covariance N (fun n => A n+R n) (fun n => B n+S n) =
      covariance N A (fun n => B n+S n)+covariance N (fun n => A n+R n) B-
        covariance N A B+covariance N R S := by
  simp only [covariance_add_left, covariance_add_right]
  ring

noncomputable def centeredFourFactor (α : ℝ) (N U V S T : ℕ) : ℝ :=
  covariance N (fun n => typeIIPart U V n) (fun n => typeIIPart S T (floorMul α n))

lemma centeredFourFactor_eq {α : ℝ} (hα : 1 ≤ α) (N U V S T : ℕ) :
    centeredFourFactor α N U V S T = fourFactorRemainder α N U V S T-
      total N (fun n => typeIIPart U V n)*total N (fun n => typeIIPart S T (floorMul α n))/N := by
  rw [centeredFourFactor, covariance, ← typeII_pair_eq_fourFactor hα]
  rfl

/-- This identity is valid without any assertion about the signs of the
individual remainder functions or their centered product. -/
theorem centered_double_vaughan_identity (α : ℝ) (N U V S T : ℕ) :
    covariance N (fun n => vonMangoldt n) (fun n => vonMangoldt (floorMul α n)) =
      covariance N (fun n => typeIPart U V n) (fun n => vonMangoldt (floorMul α n))+
        covariance N (fun n => vonMangoldt n) (fun n => typeIPart S T (floorMul α n))-
          covariance N (fun n => typeIPart U V n) (fun n => typeIPart S T (floorMul α n))+
            centeredFourFactor α N U V S T := by
  have h₁ : (fun n => vonMangoldt n) = (fun n => typeIPart U V n+typeIIPart U V n) := by
    funext n
    exact congrArg (fun f : ArithmeticFunction ℝ => f n) (mangoldt_split U V)
  have h₂ : (fun n => vonMangoldt (floorMul α n)) =
      (fun n => typeIPart S T (floorMul α n)+typeIIPart S T (floorMul α n)) := by
    funext n
    exact congrArg (fun f : ArithmeticFunction ℝ => f (floorMul α n)) (mangoldt_split S T)
  rw [h₁, h₂]
  exact covariance_double_split N _ _ _ _

#print axioms centered_double_vaughan_identity

end Erdos972CenteredDoubleVaughan
