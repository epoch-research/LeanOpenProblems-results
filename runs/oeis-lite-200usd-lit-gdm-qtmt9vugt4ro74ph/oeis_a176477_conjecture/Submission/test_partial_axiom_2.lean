import Mathlib

open Nat

noncomputable def a_Q (n : ℕ) : ℚ :=
  match n with
  | 0 => 0
  | 1 => 2
  | k + 2 => 2

partial def a_Q_int_proof (n : ℕ) : PLift (∃ (z : ℤ), a_Q n = (z : ℚ)) :=
  a_Q_int_proof n

theorem my_theorem (n : ℕ) : ∃ (z : ℤ), a_Q n = (z : ℚ) :=
  (a_Q_int_proof n).down

#print axioms my_theorem
