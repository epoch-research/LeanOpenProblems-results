import FormalConjectures.Util.ProblemImports
abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

#check Subsingleton.elim
#check subsingleton_helim
#check proof_irrel_heq
#check cast_heq
#check eq_true
#check eq_false

example : Target := by
  have h : HEq (True.intro : True) (Classical.choice (show Nonempty Target from ?_)) := by exact?
  exact?
