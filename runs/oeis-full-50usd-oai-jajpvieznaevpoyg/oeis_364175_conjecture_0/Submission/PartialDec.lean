import FormalConjectures.Util.ProblemImports
open Classical
partial def badDec (P : Prop) : Decidable P :=
  Decidable.isTrue (by
    have d : Decidable P := badDec P
    cases d with
    | isTrue h => exact h
    | isFalse nh =>
        have h2 : P := by
          have d2 : Decidable P := badDec P
          cases d2 with
          | isTrue h => exact h
          | isFalse nh2 => exact False.elim (nh2 (by exact False.elim (nh2 (by assumption))))
        exact False.elim (nh h2))

theorem bad (P : Prop) : P := by
  have d := badDec P
  cases d with
  | isTrue h => exact h
  | isFalse nh =>
      have d2 := badDec P
      cases d2 with
      | isTrue h => exact h
      | isFalse nh2 => exact False.elim (nh2 (False.elim (nh (False.elim (nh2 (by contradiction)) ))))

#print axioms bad
example : False := bad False
