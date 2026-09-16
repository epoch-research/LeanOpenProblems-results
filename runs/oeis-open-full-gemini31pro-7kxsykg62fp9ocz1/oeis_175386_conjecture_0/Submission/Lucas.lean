import Mathlib

def L : ℕ → ℕ
| 0 => 2
| 1 => 1
| (n + 2) => L (n + 1) + L n

theorem L_mod_4_even (k : ℕ) : L (2 * k) % 4 = 3 ∨ L (2 * k) % 4 = 2 := by
  sorry
