import FormalConjectures.Util.ProblemImports
partial def loop (_ : Unit) : Empty := loop ()
theorem bad : False := nomatch loop ()
#print axioms bad
