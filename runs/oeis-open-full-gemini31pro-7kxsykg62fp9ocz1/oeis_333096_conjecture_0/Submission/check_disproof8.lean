import Submission.Spec
open Nat

theorem disproof_proof : ¬ (type_of% @oeis_333096_conjecture_0) := by
  intro h
  have h1 : (a (1 * 7 ^ 1) : ℤ) ≡ a (1 * 7 ^ (1 - 1)) [ZMOD (7 ^ (3 * 1) : ℤ)] := h 7 1 1 (by decide)
  have h2 : (a (1 * 7 ^ 1) : ℤ) % (7 ^ (3 * 1) : ℤ) = (a (1 * 7 ^ (1 - 1)) : ℤ) % (7 ^ (3 * 1) : ℤ) := h1
  revert h2
  decide
