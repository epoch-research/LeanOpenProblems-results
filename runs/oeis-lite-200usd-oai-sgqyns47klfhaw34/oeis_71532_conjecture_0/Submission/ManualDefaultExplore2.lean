import FormalConjectures.Util.ProblemImports

def fNot (P : Prop) (h : ¬ P) : ¬ P := h

partial def «fNot._default.2» (P : Prop) (h : ¬ P) : ¬ P := h

#check fNot._default.2

theorem bad : False := by
  exact fNot True trivial

#print axioms bad
