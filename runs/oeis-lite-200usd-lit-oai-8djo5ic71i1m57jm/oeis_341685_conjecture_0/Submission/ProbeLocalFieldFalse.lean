import FormalConjectures.Util.ProblemImports

theorem localFieldIntFalse : False := by
  letI : Field ℤ := Classical.choice (Infinite.nonempty_field (α := ℤ))
  have hfield : (0 : ℤ) ≠ (1 : ℤ) := zero_ne_one
  have hstd : (0 : ℤ) = (1 : ℤ) := by
    norm_num
  exact hfield hstd

#print axioms localFieldIntFalse
