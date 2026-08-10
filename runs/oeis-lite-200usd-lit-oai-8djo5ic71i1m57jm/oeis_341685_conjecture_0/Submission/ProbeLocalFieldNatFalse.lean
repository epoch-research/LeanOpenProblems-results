import FormalConjectures.Util.ProblemImports

theorem localFieldNatFalse : False := by
  letI : Field ℕ := Classical.choice (Infinite.nonempty_field (α := ℕ))
  have hfield : (0 : ℕ) - 1 ≠ 0 := by
    simp
  have hnat : (0 : ℕ) - 1 = 0 := by
    norm_num
  exact hfield hnat

#print axioms localFieldNatFalse
