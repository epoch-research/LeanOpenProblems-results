import FormalConjectures.Util.ProblemImports
partial def neFalse (_ : Unit) : Nonempty False := neFalse ()
example : False := Classical.choice (neFalse ())
#print axioms neFalse
#print axioms PartialNonempty2._example
