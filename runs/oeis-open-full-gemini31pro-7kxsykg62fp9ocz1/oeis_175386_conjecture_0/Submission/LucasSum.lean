import Mathlib

def L : ℕ → ℕ
| 0 => 2
| 1 => 1
| (n + 2) => L (n + 1) + L n

theorem S_id (n : ℕ) :
  (Finset.sum (Finset.Icc 1 n) fun i => (2 * n) * Nat.choose (2 * n - i - 1) (i - 1) / i) = L (2 * n) - 1 := sorry

