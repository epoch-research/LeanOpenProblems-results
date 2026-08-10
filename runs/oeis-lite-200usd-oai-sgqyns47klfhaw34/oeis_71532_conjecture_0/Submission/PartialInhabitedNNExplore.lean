import FormalConjectures.Util.ProblemImports

partial def instNN (P : Prop) : Inhabited (¬¬P) :=
  ⟨fun h => (instNN P).default h⟩

partial def nonemptyNN (P : Prop) : Nonempty (¬¬P) :=
  ⟨fun h => (Classical.choice (nonemptyNN P)) h⟩

theorem arbitrary1 (P : Prop) : P := by
  classical
  exact Classical.byContradiction (instNN P).default

theorem arbitrary2 (P : Prop) : P := by
  classical
  exact Classical.byContradiction (Classical.choice (nonemptyNN P))

#print axioms instNN
#print axioms nonemptyNN
#print axioms arbitrary1
#print axioms arbitrary2
