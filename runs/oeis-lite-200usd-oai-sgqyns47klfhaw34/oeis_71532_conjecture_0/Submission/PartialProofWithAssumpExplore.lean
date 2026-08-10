import FormalConjectures.Util.ProblemImports

partial def fromNot (P : Prop) (hn : ¬ P) : P := fromNot P hn
partial def toFalse (P : Prop) (hp : P) : False := toFalse P hp

#print axioms fromNot
#print axioms toFalse
