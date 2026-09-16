import Submission.Spec
open Nat Finset

theorem oeis_379643_conjecture_0_proof : ∀ (n : ℕ), 0 < n → ¬ (a n = 0 ∧ b n < 0) := by
  intro n hn h
  rcases h with ⟨ha, hb⟩
  unfold a at ha
  unfold b at hb
  split at ha
  · contradiction
  · split at hb
    · contradiction
    · omega
