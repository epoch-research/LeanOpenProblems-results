import Submission.BuchstabOrderedZeta
import Submission.BuchstabSharpSource

/-! Application of the ordered-product bound to the actual canonical
Selberg source, retaining its scale factor four and every incurred error. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Real

/-- Uniform simultaneously in refinement depth, prime prefix and level.
This does not preserve the inverse-log-square saving of the fixed-depth estimate. -/
theorem sharp_refined_lowerError_le_log_uniform
    (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime) (hmono : StrictMono p)
    (n k : ℕ) (D : ℝ) (hD : 1 < D) :
    lowerErrorStep (fun i => 1/(p i : ℝ)) (primeKeep p)
      (upperError (fun i => 1/(p i : ℝ)) (primeKeep p)
        (scaledSharpSelbergCost p) n) k D ≤ 4*exp 1*D*(1+log D) := by
  exact prime_refined_lowerError_le_log_mul p hp hmono (scaledSharpSelbergCost p)
    4 (by norm_num) (fun j E hE =>
      (scaledSharpSelbergCost_le_old p hp hmono.injective j E).trans
        (scaledSelbergCost_le j E hE)) n k D hD

#print axioms sharp_refined_lowerError_le_log_uniform
end Erdos970.RecursiveSieve.Buchstab
