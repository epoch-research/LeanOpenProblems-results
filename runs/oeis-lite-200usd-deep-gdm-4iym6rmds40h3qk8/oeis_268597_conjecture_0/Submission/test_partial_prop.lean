import Mathlib

open Nat

partial def test (n : ℕ) : ∃ x > 0, (x - 1) % Nat.totient x = n := test n
