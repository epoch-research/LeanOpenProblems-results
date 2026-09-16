import Mathlib

example (A K p q : ℕ) : (A + K * (p * q)) % p = A % p := by
  have : K * (p * q) = (K * q) * p := by ring
  rw [this]
  exact Nat.add_mul_mod_self_right A (K * q) p

example (A K p q : ℕ) : (A + K * (p * q)) % q = A % q := by
  have : K * (p * q) = (K * p) * q := by ring
  rw [this]
  exact Nat.add_mul_mod_self_right A (K * p) q
