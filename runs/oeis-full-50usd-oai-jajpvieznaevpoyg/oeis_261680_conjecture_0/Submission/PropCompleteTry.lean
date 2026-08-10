import FormalConjectures.Util.ProblemImports
example (P : Prop) : P := by
  cases Classical.propComplete P with
  | inl h =>
      rw [h]
      trivial
  | inr h =>
      -- stuck: P = False
      rw [h]
