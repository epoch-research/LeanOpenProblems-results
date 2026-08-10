import FormalConjectures.Util.ProblemImports
#check Infinite.nonempty_field
#check Infinite.field
#check Field

example : Nonempty (Field ℕ) := Infinite.nonempty_field ℕ

example : False := by
  letI : Field ℕ := Classical.choice (Infinite.nonempty_field ℕ)
  -- Does this field use standard 0/1? It would imply (0:ℕ) ≠ 1, consistent.
  have h : (0 : ℕ) ≠ 1 := zero_ne_one
  norm_num at h
  guard_target = False
  sorry

#print axioms Infinite.nonempty_field
