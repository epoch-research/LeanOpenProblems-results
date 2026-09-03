import Submission.SmoothPrimeCore
import Submission.BinomialCompositeGain

/-!
# Retaining the attained above-half exponent in a smooth-prime core

This is a restriction of the inputs, not an increase of the known exponent.
-/

open Nat Filter
namespace Erdos821

/-- The existing binomial-composite range survives when every input is
squarefree and each of its prime predecessors is square-root smooth. -/
theorem infinite_gSmoothCore_two_gt_binomial (β : ℝ) (hβ0 : 1/2 ≤ β)
    (hβ : β < 1/2 + 1/(2400000*Sieve.totientRatioAverageConstant+10)) :
    {n : ℕ | (n : ℝ)^β < gSmoothCore 2 n}.Infinite := by
  let A : ℝ := 1/2 + 1/(2400000*Sieve.totientRatioAverageConstant+10)
  let γ : ℝ := (β+A)/2
  have hβγ : β < γ := by dsimp [γ, A]; linarith
  have hγA : γ < A := by dsimp [γ, A]; linarith
  exact infinite_gSmoothCore_gt_of_infinite_g_gt 2 (by omega) β γ
    (by norm_num; exact hβ0) hβγ (infinite_g_gt_binomial_composite_uniform γ hγA)

end Erdos821
