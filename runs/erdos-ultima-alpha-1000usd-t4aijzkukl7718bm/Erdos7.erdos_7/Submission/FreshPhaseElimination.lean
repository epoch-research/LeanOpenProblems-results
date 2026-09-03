import FormalConjecturesUtil

/-! Exact elimination of fresh-phase handoff variables. This is a finite
integer accounting fact, not a covering-system existence or nonexistence claim. -/
namespace Erdos7FreshPhaseElimination
set_option autoImplicit false
open Finset

theorem handoff_iff {I : Type*} [Fintype I] (incoming pure : I → ℕ)
    (oldIn oldOut : ℕ) :
    (∃ h : I → ℕ, (∀ i, pure i + h i = incoming i) ∧
      oldOut = oldIn + ∑ i, h i) ↔
    (∀ i, pure i ≤ incoming i) ∧
      oldOut + ∑ i, pure i = oldIn + ∑ i, incoming i := by
  constructor
  · rintro ⟨h, hh, ho⟩
    refine ⟨fun i => by have := hh i; omega, ?_⟩
    have hs : (∑ i, pure i) + (∑ i, h i) = ∑ i, incoming i := by
      rw [← sum_add_distrib]
      exact sum_congr rfl (fun i _ => hh i)
    omega
  · rintro ⟨hp, he⟩
    refine ⟨fun i => incoming i - pure i, ?_, ?_⟩
    · intro i
      exact Nat.add_sub_of_le (hp i)
    · have hs : (∑ i, pure i) + (∑ i, (incoming i - pure i)) =
          ∑ i, incoming i := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro i _
        exact Nat.add_sub_of_le (hp i)
      change oldOut = oldIn + ∑ i, (incoming i - pure i)
      omega

lemma handoff_unique {I : Type*} (incoming pure h : I → ℕ)
    (hh : ∀ i, pure i + h i = incoming i) :
    h = fun i => incoming i - pure i := by
  funext i
  have := hh i
  omega

#print axioms handoff_iff
#print axioms handoff_unique
end Erdos7FreshPhaseElimination
