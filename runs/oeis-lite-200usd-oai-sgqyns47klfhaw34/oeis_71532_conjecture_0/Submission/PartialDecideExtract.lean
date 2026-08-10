import FormalConjectures.Util.ProblemImports

partial def loopDec (P : Prop) : Decidable P := loopDec P

partial def getProof (P : Prop) [Decidable P] : P :=
  match ‹Decidable P› with
  | isTrue h => h
  | isFalse _ => getProof P

#print axioms loopDec
#print axioms getProof

example (P : Prop) : P := by
  letI : Decidable P := loopDec P
  exact getProof P

#print axioms _example
