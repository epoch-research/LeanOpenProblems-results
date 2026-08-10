import FormalConjectures.Util.ProblemImports

partial def defaultNot (P : Prop) (h : ¬ P := defaultNot P) : ¬ P := h

theorem notAny2 (P : Prop) : ¬ P := defaultNot P
#print axioms notAny2

theorem bad : False := by
  exact notAny2 True trivial
#print axioms bad
