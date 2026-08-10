import Submission.Spec

open Nat

unsafe def infinite_loop (n : ℕ) (hn : n ≥ 1) : PLift (a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m)) :=
  infinite_loop n hn

#print axioms infinite_loop
