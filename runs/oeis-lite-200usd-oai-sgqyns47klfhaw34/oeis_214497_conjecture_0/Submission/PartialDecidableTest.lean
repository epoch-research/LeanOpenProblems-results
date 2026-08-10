import FormalConjectures.Util.ProblemImports

partial def decP (P : Prop) : Decidable P := decP P

example (P : Prop) : Decidable P := decP P
#print axioms decP
