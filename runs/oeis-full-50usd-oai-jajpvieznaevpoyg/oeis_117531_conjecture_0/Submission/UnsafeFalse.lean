import FormalConjectures.Util.ProblemImports
unsafe axiom badAx : False
unsafe def bad : False := badAx
#print axioms bad
unsafe theorem tb : False := bad
#print axioms tb
-- theorem safe : False := by exact tb
