import Submission.Spec
open Nat

theorem disproof_proof : ¬ (type_of% @oeis_333096_conjecture_0) := by
  intro h
  have h1 : (a (1 * 5 ^ 1) : ℤ) ≡ a (1 * 5 ^ (1 - 1)) [ZMOD (5 ^ (3 * 1) : ℤ)] :=
    h 5 1 1 (by decide)
  sorry
