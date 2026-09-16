import Submission.Spec

open Nat

theorem disproof_proof : ¬ (type_of% @oeis_333096_conjecture_0) := by
  intro h
  have h1 : (a (1 * 5 ^ 1) : ℤ) ≡ a (1 * 5 ^ (1 - 1)) [ZMOD (5 ^ (3 * 1) : ℤ)] :=
    h 5 1 1 (by decide)
  have h2 : (a 5 : ℤ) ≡ a 1 [ZMOD 125] := h1
  have h3 : (111880 : ℤ) ≡ 5 [ZMOD 125] := h2
  have h4 : (111880 : ℤ) % 125 = (5 : ℤ) % 125 := h3
  revert h4
  intro h5
  have h6 : (111880 : ℤ) % 125 = 5 := rfl
  have h7 : (5 : ℤ) % 125 = 5 := rfl
  rw [h6, h7] at h5
  revert h5
  decide
