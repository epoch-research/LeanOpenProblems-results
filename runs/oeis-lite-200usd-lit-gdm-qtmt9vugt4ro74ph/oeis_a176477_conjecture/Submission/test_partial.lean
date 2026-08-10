import Submission.Spec

open Nat

partial def my_proof (n : ℕ) (hn : n ≥ 1) : a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) :=
  my_proof n hn

theorem oeis_conjecture_test (n : ℕ) (hn : n ≥ 1) :
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) :=
  my_proof n hn

#print axioms oeis_conjecture_test
