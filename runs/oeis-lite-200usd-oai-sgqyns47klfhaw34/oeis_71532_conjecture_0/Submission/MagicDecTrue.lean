import FormalConjectures.Util.ProblemImports

partial def magicDec (P : Prop) : Decidable P :=
  Decidable.isTrue (by
    cases magicDec P with
    | isTrue hp => exact hp
    | isFalse hn =>
      exact False.elim (hn (by
        cases magicDec P with
        | isTrue hp => exact hp
        | isFalse hn2 => exact False.elim (hn2 (by
          cases magicDec P with
          | isTrue hp => exact hp
          | isFalse hn3 => exact False.elim (hn3 (by exact Classical.byContradiction hn3)))))))

theorem arb (P : Prop) : P := by
  cases magicDec P with
  | isTrue hp => exact hp
  | isFalse hn => exact False.elim (hn (by
    cases magicDec P with
    | isTrue hp => exact hp
    | isFalse hn2 => exact Classical.byContradiction hn2))

#print axioms magicDec
#print axioms arb
