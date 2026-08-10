import FormalConjectures.Util.ProblemImports

abbrev ETrueProp : Prop := Classical.epsilon (fun P : Prop => P)

theorem epsilon_gives_some_true_prop : ETrueProp := by
  exact Classical.epsilon_spec (p := fun P : Prop => P) ⟨True, trivial⟩

#print axioms epsilon_gives_some_true_prop

-- Try a predicate mentioning arbitrary target.
example (Target : Prop) : (Classical.epsilon (fun P : Prop => P = Target ∨ P)) = Target ∨
    Classical.epsilon (fun P : Prop => P = Target ∨ P) := by
  exact Classical.epsilon_spec (p := fun P : Prop => P = Target ∨ P) ⟨True, Or.inr trivial⟩

example (Target : Prop) : ¬ (∀ {Target : Prop}, Target) := by
  intro h
  exact h (Target := False)

-- The epsilon facts do not close arbitrary Target.
example (Target : Prop) : Target := by
  let E := Classical.epsilon (fun P : Prop => P = Target ∨ P)
  have hE : E = Target ∨ E := Classical.epsilon_spec (p := fun P : Prop => P = Target ∨ P) ⟨True, Or.inr trivial⟩
  rcases hE with h | h
  · -- only equality, no proof of E
    fail_if_success exact h ▸ (by trivial : E)
    all_goals admit
  · -- proof of E, no equality to Target
    fail_if_success exact h
    all_goals admit
