import FormalConjectures.Util.ProblemImports

def fNot (P : Prop) (h : ¬ P) : ¬ P := h

-- Try to provide the default argument declaration manually.
partial def fNot._default.2 (P : Prop) (h : ¬ P) : ¬ P := h

theorem bad : False := by
  exact fNot True trivial

#print axioms bad
