import Mathlib

open Nat

def witness (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 4
  | 2 => 9
  | 3 => 8
  | 4 => 25
  | 5 => 18
  | _ => 1 -- default

lemma witness_spec (n : ℕ) (h : n < 6) : witness n > 0 ∧ (witness n - 1) % totient (witness n) = n := by
  interval_cases n <;> decide
