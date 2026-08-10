import FormalConjectures.Util.ProblemImports

example (P : Prop) : P := by
  rcases Classical.propComplete P with h | h
  · exact Eq.mpr h trivial
  · -- impossible branch cannot be closed
    fail_if_success exact Eq.mp h trivial
    sorry

example (P : Prop) : ¬ P := by
  rcases Classical.propComplete P with h | h
  · -- true branch cannot be closed
    sorry
  · intro hp
    have hf : False := Eq.mp h hp
    exact hf
