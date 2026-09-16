import Submission.Spec
open Nat

theorem test : ¬ (type_of% @oeis_333096_conjecture_0) := by
  intro h
  have h1 := h 13 1 1 (by decide)
  have h2 : (a 13 : ℤ) % (13 ^ 3 : ℤ) = (a 1 : ℤ) % (13 ^ 3 : ℤ) := h1
  revert h2
  decide
