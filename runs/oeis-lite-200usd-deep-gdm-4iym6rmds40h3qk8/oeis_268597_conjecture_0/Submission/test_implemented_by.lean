import Mathlib

open Nat

unsafe def test_impl (n : ℕ) : ∃ x > 0, (x - 1) % Nat.totient x = n :=
  test_impl n

@[implemented_by test_impl]
opaque test (n : ℕ) : ∃ x > 0, (x - 1) % Nat.totient x = n
