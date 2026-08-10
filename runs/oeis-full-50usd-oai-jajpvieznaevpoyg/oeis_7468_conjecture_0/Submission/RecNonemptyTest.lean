import FormalConjectures.Util.ProblemImports

-- try several impossible-looking recursive/classical constructions
-- They should fail unless Lean has a safe fixpoint for arbitrary propositions.

-- def bad1 (P : Prop) : P := bad1 P

-- noncomputable def bad2 (P : Prop) : Nonempty P := ⟨Classical.choice (bad2 P)⟩

example (P : Prop) : ¬ (Nonempty P → P) := by
  intro h
  exact h ⟨False.elim ?_⟩
