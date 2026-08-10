import FormalConjectures.Util.ProblemImports
unsafe def ufalse : False := unsafeCast ()
-- theorem safe_bad : False := ufalse
unsafe theorem unsafe_bad : False := ufalse
#print axioms unsafe_bad
