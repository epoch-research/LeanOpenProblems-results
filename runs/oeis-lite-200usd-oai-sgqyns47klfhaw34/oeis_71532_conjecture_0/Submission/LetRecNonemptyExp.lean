import FormalConjectures.Util.ProblemImports

example (P : Prop) : P := by
  let rec ne : Nonempty P := ⟨Classical.choice ne⟩
  exact Classical.choice ne

#print axioms LetRecNonemptyExp._example_1
