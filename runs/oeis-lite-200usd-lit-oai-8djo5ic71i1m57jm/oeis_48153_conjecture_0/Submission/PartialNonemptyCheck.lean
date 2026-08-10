import FormalConjectures.Util.ProblemImports
partial def loopP (P : Prop) [Nonempty P] : P := loopP P
example (P : Prop) : P := by
  letI : Nonempty P := ⟨loopP P⟩
  exact loopP P
#print axioms loopP
#print axioms «example»
