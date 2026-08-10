import FormalConjectures.Util.ProblemImports

partial def f (u : Unit) : Empty := f u

theorem bad : False := nomatch f ()
#print axioms f
#print axioms bad
