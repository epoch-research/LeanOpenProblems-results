import FormalConjectures.Util.ProblemImports

theorem t (P : Prop) : P := by
  classical
  -- exact Classical.choice (inferInstance : Nonempty P)
  aesop
