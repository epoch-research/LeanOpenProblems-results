import FormalConjectures.Util.ProblemImports
axiom P : Prop
partial def neP (_ : Unit) : Nonempty P := neP ()
#print axioms neP
partial def nneP (_ : Unit) : Nonempty (Nonempty P) := nneP ()
#print axioms nneP
partial def inhNEP (_ : Unit) : Inhabited (Nonempty P) := inhNEP ()
#print axioms inhNEP
example : P := Classical.choice (neP ())
example : P := Classical.choice (Classical.choice (nneP ()))
example : P := Classical.choice (default : Nonempty P)
