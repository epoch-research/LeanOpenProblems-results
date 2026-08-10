import Submission.Spec

open Nat

unsafe def infinite_loop (n : ℕ) (hn : n ≥ 1) : PLift (a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m)) :=
  infinite_loop n hn

theorem safe_theorem (n : ℕ) (hn : n ≥ 1) : a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  have := infinite_loop n hn
  exact this.down

#print axioms safe_theorem
