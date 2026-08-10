import FormalConjectures.Util.ProblemImports
partial def decLoop (P : Prop) : Decidable P := decLoop P

theorem decArb (P : Prop) : Decidable P := decLoop P
#print axioms decLoop
#print axioms decArb
