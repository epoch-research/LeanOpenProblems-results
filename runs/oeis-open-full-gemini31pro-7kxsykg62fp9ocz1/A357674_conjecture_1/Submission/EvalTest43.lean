import Submission.Spec
open Nat

theorem T : ∃ x : ℕ, x = 0 := by
  let _s := 0
  exact ⟨0, rfl⟩
