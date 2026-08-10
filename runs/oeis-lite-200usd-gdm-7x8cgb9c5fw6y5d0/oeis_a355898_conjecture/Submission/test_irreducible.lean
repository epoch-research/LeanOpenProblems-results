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

-- Define irreducible values
def b0_val : ℕ := B 0 - 1
def b1_val : ℕ := B 1 - 1

attribute [irreducible] b0_val b1_val

theorem test_eq : b0_val = (A355898_loop 3772 1 1).1 := by
  -- Since it is irreducible, we can still unfold it manually using unfolding or dsimp
  unfold b0_val
  simp only [B]
