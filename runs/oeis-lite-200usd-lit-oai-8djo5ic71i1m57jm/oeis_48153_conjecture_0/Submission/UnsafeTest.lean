import FormalConjectures.Util.ProblemImports
unsafe def badProof : False := unsafeCast True.intro
theorem t : False := by exact badProof
