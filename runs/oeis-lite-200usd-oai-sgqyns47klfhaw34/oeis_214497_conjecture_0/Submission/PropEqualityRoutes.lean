import FormalConjectures.Util.ProblemImports
abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

#synth Subsingleton Prop
#synth Subsingleton Sort
#synth Subsingleton (Type)

example : Target := by
  have h : (Target : Sort 0) = (True : Sort 0) := by
    exact Subsingleton.elim _ _
  exact cast h.symm True.intro

example : Target := by
  have h : HEq True.intro (show Target from ?_) := by exact HEq.rfl
  exact ?_
