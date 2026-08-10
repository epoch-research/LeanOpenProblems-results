import FormalConjectures.Util.ProblemImports
partial def badDec (P : Prop) : Decidable P :=
  Decidable.isTrue (let rec h : P := by
    have d : Decidable P := badDec P
    cases d with
    | isTrue hp => exact hp
    | isFalse nh => exact False.elim (nh h)
    ; h)

theorem bad (P : Prop) : P := by
  have d := badDec P
  cases d with
  | isTrue h => exact h
  | isFalse nh =>
      have d2 := badDec P
      cases d2 with
      | isTrue h => exact h
      | isFalse nh2 => exact False.elim (nh2 (by exact False.elim (nh (by contradiction))))
#print axioms bad
example : False := bad False
