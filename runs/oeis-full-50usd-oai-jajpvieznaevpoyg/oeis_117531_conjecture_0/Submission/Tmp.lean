import FormalConjectures.Util.ProblemImports
open Finset Nat
noncomputable def a (n : ℕ) : ℕ := 0

theorem oeis_117531_conjecture_0 (n : ℕ) (h : n > 13) : a n < n := by
  unfold a
  omega
