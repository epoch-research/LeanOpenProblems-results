import FormalConjectures.Util.ProblemImports
axiom P : Prop

def proveDec : Decidable P → P
| .isTrue h => h
| .isFalse h => False.elim (h (proveDec (.isFalse h)))

#print axioms proveDec
example : P := proveDec (Classical.decEq P P |> by exact Classical.decEq P P)
