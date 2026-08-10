import FormalConjectures.Util.ProblemImports
partial def instNonemptyFalse (_ : Unit) : Nonempty False := instNonemptyFalse ()
attribute [instance] instNonemptyFalse
example : False := Classical.choice (inferInstance : Nonempty False)
#print axioms instNonemptyFalse
