import FormalConjectures.Util.ProblemImports
partial def badF (u : Unit) : False := badF u
#print badF
#print axioms badF
example : False := badF ()
#print axioms (show False from badF ())

partial def badP (p : Prop) (u : Unit) : p := badP p u
#print badP
