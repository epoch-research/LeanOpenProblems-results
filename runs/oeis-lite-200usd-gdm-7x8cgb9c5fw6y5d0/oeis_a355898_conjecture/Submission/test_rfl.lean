import FormalConjectures.Util.ProblemImports

open Nat

def A355898_loop : ℕ → ℕ → ℕ → ℕ × ℕ
| 0, a, b => (a, b)
| n + 1, a, b =>
  let g := Nat.gcd b a
  A355898_loop n b (g + (b + a) / g)

def B0 : ℕ := (A355898_loop 3772 1 1).1 + 1
def B1 : ℕ := (A355898_loop 3772 1 1).2 + 1

theorem B0_sub_1_eq : B0 - 1 = (A355898_loop 3772 1 1).1 := by
  unfold B0
  omega

theorem B1_sub_1_eq : B1 - 1 = (A355898_loop 3772 1 1).2 := by
  unfold B1
  omega
