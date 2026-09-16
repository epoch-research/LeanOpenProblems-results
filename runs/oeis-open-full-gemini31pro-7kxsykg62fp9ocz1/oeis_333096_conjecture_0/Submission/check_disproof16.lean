import Submission.Spec
open Nat

theorem test : ¬ (type_of% @oeis_333096_conjecture_0) := by
  intro h
  have h1 := h 13 1 1 (by decide)
  revert h1
  decide
