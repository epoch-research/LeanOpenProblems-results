import FormalConjectures.Util.ProblemImports
noncomputable def proveIfComplete (P : Prop) : P := by
  rcases Classical.propComplete P with h | h
  · rw [h]; trivial
  · rw [h]
    -- target False
    exact ?x
