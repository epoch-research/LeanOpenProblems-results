import FormalConjectures.Util.ProblemImports
#check Classical.propComplete
example (P : Prop) : P := by
  rcases Classical.propComplete P with h|h
  · simpa using h
  · -- h : ¬ P? or P = False?
    guard_target = P
    fail_if_success exact h
    sorry
