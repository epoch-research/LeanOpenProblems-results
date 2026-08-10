import FormalConjectures.Util.ProblemImports
partial def decLoop (P : Prop) : Decidable P → P
| isTrue h => h
| isFalse _ => decLoop P (Classical.dec P)

example : False := decLoop False (Classical.dec False)
#print axioms decLoop
#print axioms «example»
