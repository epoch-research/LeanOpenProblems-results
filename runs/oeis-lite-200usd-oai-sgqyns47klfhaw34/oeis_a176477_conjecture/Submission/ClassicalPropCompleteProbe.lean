import FormalConjectures.Util.ProblemImports
#check Classical.propComplete
example : ¬ (False = True) := by intro h; exact Eq.mp h False.elim
-- Try prove arbitrary P? should fail
example (P : Prop) : P := by
  rcases Classical.propComplete P with h | h
  · -- P = True
    exact Eq.mp h.symm True.intro
  · -- P = False, impossible only if P known true
    -- stuck
    sorry
