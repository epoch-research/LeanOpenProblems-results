import FormalConjectures.Util.ProblemImports
partial def trickyDec (P : Prop) : Decidable P :=
  Decidable.isTrue (by
    let rec loop : P := by
      have d := trickyDec P
      cases d with
      | isTrue h => exact h
      | isFalse hn => exact False.elim (hn loop)
    exact loop)

theorem bad (P : Prop) : P := by
  have d := trickyDec P
  cases d with
  | isTrue h => exact h
  | isFalse hn =>
      have d2 := trickyDec P
      cases d2 with
      | isTrue h => exact h
      | isFalse hn2 => exact False.elim (hn2 (by
          -- try use local recursive proof too
          let rec loop : P := by exact False.elim (hn loop)
          exact loop))
#print axioms trickyDec
#print axioms bad
example : False := bad False
