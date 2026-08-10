import FormalConjectures.Util.ProblemImports

partial def negToProof (P : Prop) (h : ¬ P) : P := negToProof P h
#print negToProof
#print axioms negToProof

example (P : Prop) : P := by
  classical
  by_contra h
  exact h (negToProof P h)
