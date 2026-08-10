import FormalConjectures.Util.ProblemImports

example (P : Prop) : Subsingleton (Decidable P) := by infer_instance

example (P : Prop) : P := by
  classical
  have h : (isTrue trivial : Decidable True) = (Classical.decEq True True ▸ inferInstance : Decidable True) := by
    apply Subsingleton.elim
  -- placeholder
  by_cases hp : P
  · exact hp
  · exact False.elim (hp ?_)
