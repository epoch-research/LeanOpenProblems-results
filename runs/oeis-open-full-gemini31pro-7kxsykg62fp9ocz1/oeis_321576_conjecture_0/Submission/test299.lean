import FormalConjectures.Util.ProblemImports

theorem sInf_empty_eq : sInf (∅ : Set ℕ) = 0 := by
  exact Nat.sInf_empty
