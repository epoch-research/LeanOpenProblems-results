import FormalConjectures.Util.ProblemImports

open Nat

def P : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
    let (x, y) := P n
    (x - (n + 1) * y, (n + 1) * x + y)

theorem P_norm_pos (n : ℕ) : (P n).1^2 + (P n).2^2 > 0 := sorry

lemma a_ne_zero_0 (n : ℕ) (hn : n ≥ 4) (h0 : n % 4 = 0) : (P n).2 ≠ 0 := by
  sorry
