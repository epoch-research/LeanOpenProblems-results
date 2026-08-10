import Mathlib

open Nat

lemma gcd_step_eq (a b : ℕ) : Nat.gcd (1 + a + b) a = Nat.gcd (1 + b) a := by
  have h1 : 1 + a + b = (1 + b) + a := by omega
  rw [h1]
  rw [Nat.gcd_add_self_left]
