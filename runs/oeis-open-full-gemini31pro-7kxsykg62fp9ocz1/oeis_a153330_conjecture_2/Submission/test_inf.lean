import FormalConjectures.Util.ProblemImports
open Set

theorem empty_sInf : sInf (∅ : Set ℕ) = 0 := by
  exact Nat.sInf_empty
