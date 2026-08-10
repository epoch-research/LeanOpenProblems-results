import FormalConjectures.Util.ProblemImports

abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

example : HEq True.intro (Classical.choice (Classical.dec Target)) := by
  exact proof_irrel_heq _ _

example : Target := by
  have hheq : HEq True.intro (Classical.choice (Classical.dec Target)) := proof_irrel_heq _ _
  exact?

example : Target := by
  have h : (True : Prop) = Target := by
    exact Subsingleton.elim _ _
  exact Eq.mp h True.intro

example : Target := by
  have h : Nonempty Target := by
    exact Classical.choice (Classical.dec (Nonempty Target))
  exact Classical.choice h
