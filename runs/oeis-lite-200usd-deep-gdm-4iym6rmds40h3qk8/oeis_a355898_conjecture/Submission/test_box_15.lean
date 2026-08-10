import Mathlib

def G_prop (n : ℕ) (m : ℕ) : Prop :=
  Nat.gcd (n - m) (n - 1 - m) = 1

example (n m' : ℕ) (h : m' + 1 + 3774 ≤ n) : G_prop (n - 1) m' = G_prop n (m' + 1) := by
  unfold G_prop
  have h1 : n - 1 - m' = n - (m' + 1) := by omega
  have h2 : n - 1 - 1 - m' = n - 1 - (m' + 1) := by omega
  rw [h1, h2]
