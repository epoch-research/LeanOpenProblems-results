import Submission.DensityReduction

/-!
# The finite obstruction required for a disproof

This is a quantifier-level characterization only. It does not establish the
obstruction, and it does not use either admitted theorem in `Submission.Spec`.
-/

namespace Erdos39

open Filter Asymptotics

/-- Negating the verified compactness reduction requires an actual finite cutoff
obstruction for every proposed near-square-root profile. -/
theorem sidon_disproof_iff_finite_prefix_obstruction :
    (¬ (∃ A : Set ℕ, A.Infinite ∧ IsSidon A ∧
      ∀ ε : ℝ, 0 < ε →
        (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2 - ε)) =O[atTop]
          (fun N => ((Set.Icc 1 N ∩ A).ncard : ℝ)))) ↔
    ∀ b : ℕ → ℕ, NearSquareRootProfile b →
      ∃ K : ℕ, ∀ B : Finset ℕ, IsSidon (B : Set ℕ) →
        ∃ N : ℕ, N ≤ K ∧ (Set.Icc 1 N ∩ (B : Set ℕ)).ncard < b N := by
  classical
  rw [sidon_growth_iff_finite_prefix_profile]
  push_neg
  rfl

#print axioms sidon_disproof_iff_finite_prefix_obstruction

end Erdos39
