import Submission.Spec
open Mathlib

theorem oeis_79727_conjecture_2_test {p : ℕ} (h_prime_in_A003625 : IsInA003625 p) :
  a (p * (p - 1)) ≡ p ^ 2 [MOD p ^ 3] := by
  exact?
