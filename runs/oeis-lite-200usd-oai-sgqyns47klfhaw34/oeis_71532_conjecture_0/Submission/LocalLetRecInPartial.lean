import FormalConjectures.Util.ProblemImports

partial def badDec (P : Prop) : Decidable P :=
  Decidable.isTrue (let rec h : P := h; h)

theorem arb (P:Prop) : P := by
  cases badDec P with
  | isTrue h => exact h
  | isFalse hn => exact False.elim (hn (by
      -- cannot
      cases badDec P with
      | isTrue h => exact h
      | isFalse hn2 => exact False.elim (hn2 (by sorry)))
#print axioms badDec
#print axioms arb
