import FormalConjectures.Util.ProblemImports

partial def magicDec (P : Prop) : Decidable P :=
  Decidable.isTrue <| by
    cases magicDec P with
    | isTrue h => exact h
    | isFalse hn =>
        -- try recursively extract once more
        cases magicDec P with
        | isTrue h => exact h
        | isFalse hn2 => exact False.elim (hn2 (False.elim (hn (by exact False.elim (hn2 (by contradiction))))) )

#print magicDec
#print axioms magicDec

example (P : Prop) : P := by
  change (match magicDec P with | isTrue h => P | isFalse h => P)
  cases magicDec P with
  | isTrue h => exact h
  | isFalse hn =>
      -- can we unfold magicDec?
      fail_if_success unfold magicDec at hn
      sorry
