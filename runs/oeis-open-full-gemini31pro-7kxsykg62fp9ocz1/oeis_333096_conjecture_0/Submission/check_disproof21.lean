import Submission.Spec
open Nat

theorem disproof_proof : ¬ (type_of% @oeis_333096_conjecture_0) := by
  intro h
  have h1 : (a (2 * 5 ^ 1) : ℤ) ≡ a (2 * 5 ^ (1 - 1)) [ZMOD (5 ^ (3 * 1) : ℤ)] :=
    h 5 1 2 (by decide)
  have h2 : (a 10 : ℤ) ≡ a 2 [ZMOD 125] := h1
  have h3 : (58770091928 : ℤ) ≡ 53 [ZMOD 125] := h2
  have h4 : (58770091928 : ℤ) % 125 = (53 : ℤ) % 125 := h3
  revert h4
  decide
