import FormalConjectures.Util.ProblemImports
#check Nat.not_isField
#check Int.not_isField
example : False := by
  letI : Field ℕ := Classical.choice (Infinite.nonempty_field (α := ℕ))
  -- Try contradiction with Nat.not_isField
  exact Nat.not_isField (inferInstance : IsField ℕ)
