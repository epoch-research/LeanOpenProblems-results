import FormalConjectures.Util.ProblemImports
open Set

theorem sInf_empty_eq_zero : sInf (∅ : Set ℕ) = 0 := by
  exact sInf_empty

#eval sInf (∅ : Set ℕ)
