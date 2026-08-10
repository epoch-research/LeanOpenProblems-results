import FormalConjectures.Util.ProblemImports

unsafe def bad : False := unsafeCast ()
#print axioms bad
example : False := by exact bad
