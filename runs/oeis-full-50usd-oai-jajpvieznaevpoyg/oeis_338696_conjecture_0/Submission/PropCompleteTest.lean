import FormalConjectures.Util.ProblemImports

example (p : Prop) : p := by
  rcases Classical.propComplete p with hp | hp
  · -- hp : p = True
    rw [hp]
    trivial
  · -- hp : p = False
    -- cannot prove p
    rw [hp]
    -- exact False.elim ?_
    sorry
