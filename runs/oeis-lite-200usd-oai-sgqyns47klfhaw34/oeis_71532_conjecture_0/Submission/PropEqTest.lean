import FormalConjectures.Util.ProblemImports

example (P : Prop) : True = P := by
  by_cases h : True = P
  · exact h
  · exfalso
    exact h (propext ⟨fun _ => by trivial, fun hp => trivial⟩)

example (P : Prop) : P := by
  have h : True = P := by
    by_cases h : True = P
    · exact h
    · exfalso
      exact h (propext ⟨fun _ => by trivial, fun hp => trivial⟩)
  exact Eq.mp h trivial
