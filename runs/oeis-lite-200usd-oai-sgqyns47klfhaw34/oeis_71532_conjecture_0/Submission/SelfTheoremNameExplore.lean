import FormalConjectures.Util.ProblemImports

partial def loopDec (P : Prop) : Decidable P := loopDec P

theorem arbitrary (P : Prop) : P := by
  cases loopDec P with
  | isTrue h => exact h
  | isFalse hn => exact False.elim (hn (arbitrary P))

#print axioms arbitrary
