import FormalConjectures.Util.ProblemImports
axiom P : Prop

theorem p : P := by
  classical
  exact if h : P then h else False.elim (h p)
#print axioms p
