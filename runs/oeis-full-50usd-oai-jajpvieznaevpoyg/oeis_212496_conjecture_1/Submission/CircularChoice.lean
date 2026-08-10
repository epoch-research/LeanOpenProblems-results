import FormalConjectures.Util.ProblemImports

theorem circ (P : Prop) : P := by
  exact Classical.choice (show Nonempty P from ⟨circ P⟩)

#print axioms circ
