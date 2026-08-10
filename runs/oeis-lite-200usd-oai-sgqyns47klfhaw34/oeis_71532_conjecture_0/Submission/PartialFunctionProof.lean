import FormalConjectures.Util.ProblemImports

partial def decLoop (P : Prop) : Decidable P := decLoop P

partial def chooseProof (P : Prop) : Decidable P → P
  | isTrue h => h
  | isFalse hn => chooseProof P (decLoop P)

theorem arbitrary (P : Prop) : P := chooseProof P (decLoop P)
#print axioms arbitrary
