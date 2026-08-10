import FormalConjectures.Util.ProblemImports

-- Try term-level letrec/mutual cycles in proof terms.
example : False := by
  let rec f : False := f
  exact f

#print axioms CycleProofProbe._example
