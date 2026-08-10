import FormalConjectures.Util.ProblemImports

-- Can prop completeness prove an arbitrary proposition? It should not.
example (P : Prop) : P := by
  classical
  rcases Classical.propComplete P with h | h
  · -- P = True
    exact Eq.mpr h trivial
  · -- P = False; impossible to finish without P being false
    fail_if_success exact Eq.mpr h False.elim
    sorry
