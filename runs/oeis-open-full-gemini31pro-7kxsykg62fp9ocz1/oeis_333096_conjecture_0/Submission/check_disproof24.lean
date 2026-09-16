import Submission.Spec
open Nat

theorem disproof_proof : ¬ (type_of% @oeis_333096_conjecture_0) := by
  intro h
  have h1 : (a (1 * 11 ^ 1) : ℤ) ≡ a (1 * 11 ^ (1 - 1)) [ZMOD (11 ^ (3 * 1) : ℤ)] :=
    h 11 1 1 (by decide)
  have h2 : (a 11 : ℤ) % (11 ^ 3 : ℤ) = (a 1 : ℤ) % (11 ^ 3 : ℤ) := h1
  revert h2
  decide
