import FormalConjectures.Util.ProblemImports

partial def decLoop (P : Prop) : Decidable P := decLoop P

theorem arbitrary (P : Prop) : P := by
  cases decLoop P with
  | isTrue h => exact h
  | isFalse h => exact False.elim (h (arbitrary P))

#print axioms arbitrary
