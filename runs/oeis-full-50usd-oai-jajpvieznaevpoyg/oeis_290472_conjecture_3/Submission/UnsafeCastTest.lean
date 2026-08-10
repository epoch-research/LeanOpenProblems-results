import FormalConjectures.Util.ProblemImports
unsafe theorem t : False := by exact unsafeCast True.intro
#print axioms t
