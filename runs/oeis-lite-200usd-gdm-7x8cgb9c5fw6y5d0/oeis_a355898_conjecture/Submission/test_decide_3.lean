import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

open Nat

def A355898_loop : ℕ → ℕ → ℕ → ℕ × ℕ
| 0, a, b => (a, b)
| n + 1, a, b =>
  let g := Nat.gcd b a
  A355898_loop n b (g + (b + a) / g)

def B : ℕ → ℕ
| 0 => (A355898_loop 3772 1 1).1 + 1
| 1 => (A355898_loop 3772 1 1).2 + 1
| k + 2 => B (k + 1) + B k

theorem base_gcd_2 : Nat.gcd (B 1) (B 0 - 1) = 1 := by
  decide
