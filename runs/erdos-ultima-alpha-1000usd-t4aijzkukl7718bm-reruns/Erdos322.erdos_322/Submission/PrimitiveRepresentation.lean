import Submission.Spec

/-! Primitive representation counts, separated from the conjecture statement. -/
namespace Erdos322

/-- Ordered representations with no common factor in all their coordinates. -/
def primitiveRepresentationCount (k n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k → Fin (n + 1))).filter
    (fun a ↦ (∑ i, (a i : ℕ) ^ k = n) ∧
      (Finset.univ : Finset (Fin k)).gcd (fun i ↦ (a i : ℕ)) = 1)).card

theorem primitiveRepresentationCount_le (k n : ℕ) :
    primitiveRepresentationCount k n ≤ representationCount k n := by
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact ha.1

end Erdos322
