import FormalConjectures.Util.ProblemImports
open Nat

theorem test_subset (S : Set ℕ) (hS : ∀ x ∈ S, x < 5948) : S.Finite := by
  apply Set.Finite.subset (Set.finite_Iio 5948)
  intro x hx
  simp only [Set.mem_Iio]
  exact hS x hx
