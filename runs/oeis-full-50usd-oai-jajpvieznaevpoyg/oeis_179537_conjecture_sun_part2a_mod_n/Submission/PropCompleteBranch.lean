import FormalConjectures.Util.ProblemImports
example (P : Prop) : P := by
  cases Classical.propComplete P with
  | inl h => exact Eq.mp h True.intro
  | inr h =>
    -- impossible generally
    fail_if_success exact False.elim (by simpa using h)
    sorry
