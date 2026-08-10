import FormalConjectures.Util.ProblemImports

partial def badNonempty (P : Prop) : Nonempty P := ⟨bad P⟩
partial def bad (P : Prop) : P := (badNonempty P).some

example : False := bad False
#print axioms bad
#print axioms badNonempty
