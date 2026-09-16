import Mathlib

def a : ℕ → ℕ
| 0 => 0
| 1 => 2
| n + 1 =>
  let current_idx := n + 1
  let prev_a := a n
  if current_idx % 2 = 0 then
    prev_a + Nat.gcd current_idx prev_a
  else
    prev_a + Nat.gcd (current_idx - 2) prev_a

def d (n : ℕ) : ℕ := a n - a (n-1)

def is_greater_twin_prime (p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (p - 2)

def is_difference_record (R : ℕ) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ d n = R ∧ (∀ k : ℕ, 2 ≤ k ∧ k < n → d k < R)

theorem oeis_166944_conjecture_0 :
  ∀ R : ℕ, 5 < R → is_difference_record R → is_greater_twin_prime R := by
  sorry
