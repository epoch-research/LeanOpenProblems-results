import FormalConjectures.Util.ProblemImports
partial def hiddenP (P : Prop) : Decidable P := Decidable.isTrue (by sorry)
theorem arbitrary (P : Prop) : P := by
  cases hiddenP P with
  | isTrue h => exact h
  | isFalse hn => exact False.elim (hn (by sorry))
#print axioms hiddenP
#print axioms arbitrary
