import Mathlib

open Nat

lemma val_q (X c q : ℕ) (h1 : q * c ≤ X) (h2 : X < (q + 1) * c) : X / c = q := by
  refine Nat.div_eq_of_lt_le h1 h2
