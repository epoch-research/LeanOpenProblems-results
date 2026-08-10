import FormalConjectures.Util.ProblemImports

partial def decLoop (P : Prop) : Decidable P := decLoop P
partial def decTrueKnown : Decidable True := Decidable.isTrue trivial
partial def decTrueKnownFun (_ : Unit) : Decidable True := Decidable.isTrue trivial

#reduce decLoop True
#reduce decTrueKnown
#reduce decTrueKnownFun ()
#eval (match decTrueKnownFun () with | isTrue _ => true | isFalse _ => false)
#print decLoop
#print decTrueKnownFun
#print axioms decTrueKnownFun
