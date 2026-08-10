import Mathlib

open Nat

partial def my_a_int (n : Nat) : Int :=
  my_a_int n

theorem my_theorem (n : Nat) : ∃ (z : Int), (z : Rat) = (my_a_int n : Rat) := by
  use my_a_int n

#print axioms my_theorem

