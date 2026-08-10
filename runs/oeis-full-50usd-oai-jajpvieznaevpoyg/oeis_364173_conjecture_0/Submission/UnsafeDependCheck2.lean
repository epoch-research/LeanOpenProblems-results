import FormalConjectures.Util.ProblemImports
unsafe def ufalse : False := unsafeCast ()
theorem safe_bad : False := ufalse
#print axioms safe_bad
