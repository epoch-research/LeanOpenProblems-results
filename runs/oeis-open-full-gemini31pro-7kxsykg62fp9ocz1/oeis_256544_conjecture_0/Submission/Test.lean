import FormalConjectures.Util.ProblemImports

open Nat Finset

def triangular (x : ℕ) : ℕ := x * (x + 1) / 2

theorem oeis_256544_conjecture_0 (m : ℕ) (hm : m > 0) (n : ℕ) :
    ∃ x y z : ℕ, n = triangular x / m + triangular y / m + triangular z / m := by
  sorry



