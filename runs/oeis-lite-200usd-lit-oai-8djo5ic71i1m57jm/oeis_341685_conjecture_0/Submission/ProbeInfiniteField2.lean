import FormalConjectures.Util.ProblemImports

example : Nonempty (Field ℕ) := (Infinite.nonempty_field (α := ℕ))

example : False := by
  letI : Field ℕ := Classical.choice (Infinite.nonempty_field (α := ℕ))
  have h : (0 : ℕ) ≠ 1 := zero_ne_one
  -- Standard norm_num should close if h is true, no contradiction.
  guard_target = False
  fail_if_success exact h rfl
  sorry

example : (0 : ℕ) = 1 := by
  letI : Field ℕ := Classical.choice (Infinite.nonempty_field (α := ℕ))
  fail_if_success exact (zero_eq_one_iff).mpr ?_
  sorry
