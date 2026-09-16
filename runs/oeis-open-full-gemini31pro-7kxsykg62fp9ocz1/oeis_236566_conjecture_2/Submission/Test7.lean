import Mathlib
import Submission.Spec

def S := {p : ℕ | Nat.Prime p ∧ Nat.Prime (Nat.nth Nat.Prime (p + 1) + 2)}

lemma S_infinite (h : a236566_conjecture_part_ii) : Set.Infinite S := by
  intro h_fin
  have h_finset : ∃ F : Finset ℕ, ∀ x, x ∈ F ↔ x ∈ S := h_fin.exists_finset
  rcases h_finset with ⟨F, hF⟩
  -- now we can take the max of F.
  let N := F.max' sorry
  sorry
