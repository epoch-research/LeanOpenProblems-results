import Mathlib

set_option maxRecDepth 200000
open Nat

def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

#eval x_seq 34 % 5

lemma prime_lt_13_cases {q : ℕ} (hq : Nat.Prime q) (h_lt : q < 13) :
    q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 11 := by
  interval_cases q
  · contradiction
  · contradiction
  · left; rfl
  · right; left; rfl
  · contradiction
  · right; right; left; rfl
  · contradiction
  · right; right; right; left; rfl
  · contradiction
  · contradiction
  · contradiction
  · right; right; right; right; rfl
  · contradiction

