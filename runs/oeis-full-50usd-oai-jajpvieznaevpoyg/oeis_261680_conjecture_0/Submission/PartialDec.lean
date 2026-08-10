import FormalConjectures.Util.ProblemImports
partial def fakeDec (P : Prop) : Decidable P := fakeDec P
#print axioms fakeDec
partial def fakeProof (P : Prop) : Decidable P → P
  | isTrue p => p
  | isFalse _ => fakeProof P (fakeDec P)
theorem bad : False := fakeProof False (fakeDec False)
#print axioms fakeProof
#print axioms bad
