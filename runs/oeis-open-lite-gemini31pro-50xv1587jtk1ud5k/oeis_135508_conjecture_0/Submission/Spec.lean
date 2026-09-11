import FormalConjectures.Util.ProblemImports

open Nat

def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

def A135508 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let x_n_plus_1 := x_seq (n + 1)
    let x_n := x_seq n
    (x_n_plus_1 / x_n) - 2

theorem oeis_135508_conjecture_0 :
  ∀ p : ℕ, Nat.Prime p → ¬ (Nat.Prime (p - 2)) → A135508 (p - 1) = p := by
  sorry

theorem oeis_135508_conjecture_0.disproof : ¬ (∀ p : ℕ, Nat.Prime p → ¬ (Nat.Prime (p - 2)) → A135508 (p - 1) = p) := by
  sorry
