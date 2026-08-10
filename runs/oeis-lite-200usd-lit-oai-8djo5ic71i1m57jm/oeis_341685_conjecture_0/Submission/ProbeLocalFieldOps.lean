import FormalConjectures.Util.ProblemImports

-- Try ℕ
example : False := by
  letI : Field ℕ := Classical.choice (Infinite.nonempty_field (α := ℕ))
  have hfield : (0 : ℕ) - 1 ≠ 0 := by
    -- field subtraction should make -1 nonzero? try
    fail_if_success exact sub_ne_zero.mpr (zero_ne_one : (0:ℕ) ≠ 1)
    fail_if_success simp
    sorry
  have hnat : (0 : ℕ) - 1 = 0 := by
    norm_num
  exact hfield hnat

-- Try deriving directly with field theorem and norm_num
example : False := by
  letI : Field ℕ := Classical.choice (Infinite.nonempty_field (α := ℕ))
  have h : (0 : ℕ) - 1 = 0 := by norm_num
  have h2 : (0 : ℕ) - 1 = -(1 : ℕ) := by rw [zero_sub]
  have h3 : -(1 : ℕ) ≠ 0 := by simpa using (neg_ne_zero.mpr (zero_ne_one : (1 : ℕ) ≠ 0))
  exact h3 (h2 ▸ h)
