import FormalConjectures.Util.ProblemImports

theorem sInf_empty_eq_bot : sInf (∅ : Set ℕ) = 0 := by
  exact Real.sInf_empty -- no, for Nat it's Nat.sInf_empty?
