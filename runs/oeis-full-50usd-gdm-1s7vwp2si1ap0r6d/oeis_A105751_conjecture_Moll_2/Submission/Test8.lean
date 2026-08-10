import Mathlib

def P : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
    let (x, y) := P n
    (x - (n + 1) * y, (n + 1) * x + y)

theorem P_norm (n : ℕ) : (P n).1^2 + (P n).2^2 = (Finset.range (n + 1)).prod (fun k ↦ 1 + (k : ℤ)^2) := by
  induction n with
  | zero =>
    simp [P]
  | succ n ih =>
    rw [Finset.prod_range_succ, ← ih]
    simp [P]
    ring
