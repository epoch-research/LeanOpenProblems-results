import Submission.Spec
open Nat

lemma test_G_from_R : ¬ (goldbach_binary_conjecture ↔ ¬ ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n) := by
  -- We know the right side is False, because 0 is a square and a 0 = 2.
  have h_RHS : ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n := by
    use 0
    exact ⟨⟨0, rfl⟩, rfl⟩
  
  -- The statement says G ↔ False.
  -- To disprove this, we must prove G!
  -- Since Goldbach is an open conjecture, maybe there is a trivial theorem in mathlib?
  sorry
