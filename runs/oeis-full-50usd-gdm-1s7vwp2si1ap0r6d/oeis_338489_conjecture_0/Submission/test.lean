import FormalConjectures.Util.ProblemImports
open Nat Int

def is_triangular (x : ℕ) : Prop :=
  ∃ k : ℕ, x = k * (k + 1) / 2

theorem oeis_338489_conjecture_0_right (n : ℕ) (h : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 5) : is_triangular n.factorial := by
  rcases h with rfl | rfl | rfl | rfl
  · use 1
    rfl
  · use 1
    rfl
  · use 3
    rfl
  · use 15
    rfl
