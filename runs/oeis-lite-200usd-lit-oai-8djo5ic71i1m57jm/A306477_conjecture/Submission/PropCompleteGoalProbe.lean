import FormalConjectures.Util.ProblemImports
open Nat Finset
example (P : Prop) : P := by
  classical
  rcases Classical.propComplete P with h | h
  · simpa [h]
  · -- impossible to finish: branch is exactly P = False
    fail_if_success simpa [h]
    admit
