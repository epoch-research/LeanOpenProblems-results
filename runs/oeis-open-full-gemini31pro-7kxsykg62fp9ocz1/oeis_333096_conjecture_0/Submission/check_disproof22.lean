import Submission.Spec
open Nat

theorem disproof_proof : ¬ (type_of% @oeis_333096_conjecture_0) := by
  intro h
  have h1 : (a (3 * 5 ^ 1) : ℤ) ≡ a (3 * 5 ^ (1 - 1)) [ZMOD (5 ^ (3 * 1) : ℤ)] :=
    h 5 1 3 (by decide)
  have h2 : (a 15 : ℤ) % 125 = (a 3 : ℤ) % 125 := h1
  revert h2
  decide
