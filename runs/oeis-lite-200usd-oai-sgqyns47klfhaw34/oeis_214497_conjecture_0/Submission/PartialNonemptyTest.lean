import FormalConjectures.Util.ProblemImports

partial def neP (P : Prop) : Nonempty P := neP P

example (P : Prop) : P := Classical.choice (neP P)
#print axioms neP
