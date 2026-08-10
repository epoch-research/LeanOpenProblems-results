import FormalConjectures.Util.ProblemImports

example (P : Prop) : P := by
  classical
  rcases Classical.propComplete P with h | h
  · simpa [h]
  · -- h : P = False
    fail_if_success exact (Eq.mp h ?_)
    sorry

example (P : Prop) : ¬¬P → P := by
  classical
  intro h
  by_cases hp : P
  · exact hp
  · exact False.elim (h hp)

example (P : Prop) : ¬¬P := by
  classical
  intro h
  -- no way
  sorry
