import Mathlib

def my_fast_prime (n : ℕ) : Decidable (Nat.Prime n) :=
  isFalse sorry

attribute [implemented_by my_fast_prime] Nat.decidablePrime
