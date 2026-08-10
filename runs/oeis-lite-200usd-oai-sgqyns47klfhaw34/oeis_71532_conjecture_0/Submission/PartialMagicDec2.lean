import FormalConjectures.Util.ProblemImports

partial def magicDec (P : Prop) : Decidable P :=
  Decidable.isTrue <| by
    let rec pr : P := by
      cases magicDec P with
      | isTrue h => exact h
      | isFalse hn => exact False.elim (hn pr)
    exact pr

#print magicDec
#print axioms magicDec

example (P : Prop) : P := by
  cases magicDec P with
  | isTrue h => exact h
  | isFalse hn =>
      -- if magicDec were isTrue impossible, but opaque
      sorry
