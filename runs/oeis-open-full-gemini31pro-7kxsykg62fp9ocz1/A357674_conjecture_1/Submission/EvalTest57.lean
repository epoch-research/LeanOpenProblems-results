import Submission.Spec
open Nat

theorem T : ∃ x : ℕ, x = 0 :=
  by exact ⟨0, rfl⟩
