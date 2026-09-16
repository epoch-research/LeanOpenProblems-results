import Mathlib

open Nat Finset

def A005259_seq (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k ↦ (n.choose k) ^ 2 * ((n + k).choose k) ^ 2

def A005258_seq (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k ↦ (n.choose k) ^ 2 * ((n + k).choose k)

def a (n : ℕ) : ℕ :=
  5 * A005259_seq n + 14 * A005258_seq (n - 1)

theorem a_test : ∀ (p : ℕ), Nat.Prime p → 5 ≤ p → (a p) ≡ (a 1) [MOD p^5] := by
  exact?
