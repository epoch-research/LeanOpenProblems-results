import Submission.Spec
open Nat Finset

theorem proof_sum : ∀ n : ℕ, A253187 n > 0 := by
  intro n
  cases n with
  | zero =>
    -- A253187 0 = 1
    sorry
  | succ n =>
    -- n >= 1
    sorry
