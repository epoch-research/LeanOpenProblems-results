import Mathlib
open Nat
example (a b c : ℕ) (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b - c := Nat.dvd_sub' h1 h2
example (x y z : ℕ) (H : Nat.Coprime x y) (H1 : x ∣ z) (H2 : y ∣ z) : x*y ∣ z := Nat.Coprime.mul_dvd_of_dvd_of_dvd H H1 H2
example (a b : ℕ) : (a : ZMod b) = 0 ↔ b ∣ a := ZMod.natCast_eq_zero_iff a b
example (x : ZMod 67) (d k: ℕ) (hx : x^d=1) : x^k = x^(k%d) := by
  conv_lhs => rw [← Nat.div_add_mod k d, pow_add, pow_mul, hx, one_pow, one_mul]
