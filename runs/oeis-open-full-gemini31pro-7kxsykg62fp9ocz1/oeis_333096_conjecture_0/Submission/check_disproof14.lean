import Submission.Spec
open Nat

theorem disproof_proof : ¬ (type_of% @oeis_333096_conjecture_0) := by
  intro h
  have h1 : (a (1 * 13 ^ 1) : ℤ) ≡ a (1 * 13 ^ (1 - 1)) [ZMOD (13 ^ (3 * 1) : ℤ)] :=
    h 13 1 1 (by decide)
  have h2 : (a 13 : ℤ) ≡ a 1 [ZMOD (13 ^ 3 : ℤ)] := h1
  sorry
