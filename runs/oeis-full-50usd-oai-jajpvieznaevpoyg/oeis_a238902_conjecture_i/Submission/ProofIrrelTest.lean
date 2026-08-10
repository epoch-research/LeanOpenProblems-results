import FormalConjectures.Util.ProblemImports

example (P Q : Prop) (h : P = Q) (hp : P) : Q := by
  simpa [h] using hp

-- Can equality to True be extracted classically and used constructively?
example (P : Prop) : P ∨ ¬ P := Classical.em P

-- This should fail: propComplete alone cannot prove arbitrary P.
example (P : Prop) : P := by
  rcases Classical.propComplete P with h | h
  · simpa [h]
  · -- goal P, h : P = False
    fail_if_success simpa [h]
    exact False.elim (by contradiction)
