import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 5000

open Nat

def A355898_loop : ℕ → ℕ → ℕ → ℕ × ℕ
| 0, a, b => (a, b)
| n + 1, a, b =>
  let g := Nat.gcd b a
  A355898_loop n b (g + (b + a) / g)

def B0 : ℕ := (A355898_loop 3772 1 1).1 + 1
def B1 : ℕ := (A355898_loop 3772 1 1).2 + 1
def A3772 : ℕ := (A355898_loop 3771 1 1).1

def B : ℕ → ℕ
| 0 => B0
| 1 => B1
| k + 2 => B (k + 1) + B k

theorem A3772_identity : A3772 + 1 = B 1 - B 0 := by
  unfold A3772 B B1 B0
  decide
