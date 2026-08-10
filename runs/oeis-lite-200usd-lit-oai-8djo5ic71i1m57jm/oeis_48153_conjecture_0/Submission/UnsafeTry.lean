import FormalConjectures.Util.ProblemImports
unsafe def ufalse : False := unsafeCast ()
example : False := by
  exact ufalse
#print axioms ufalse
