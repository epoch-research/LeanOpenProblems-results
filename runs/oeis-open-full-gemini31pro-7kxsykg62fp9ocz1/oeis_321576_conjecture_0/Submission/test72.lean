import FormalConjectures.Util.ProblemImports
open Set

theorem sInf_empty_eq : sInf (∅ : Set ℕ) = 0 := by
  exact csInf_empty
