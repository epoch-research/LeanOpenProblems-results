import FormalConjectures.Util.ProblemImports

example : False := by
  letI : Field ℤ := Classical.choice (Infinite.nonempty_field (α := ℤ))
  have hfield : (0 : ℤ) ≠ (1 : ℤ) := zero_ne_one
  have hstd : (0 : ℤ) = (1 : ℤ) := by
    -- try if local field numerals differ from standard, norm_num should not prove false equality
    fail_if_success norm_num
    -- maybe field_simp?
    fail_if_success ring
    sorry
  exact hfield hstd

example : (0 : ℤ) = Int.ofNat 0 := by rfl
example : (1 : ℤ) = Int.ofNat 1 := by rfl
