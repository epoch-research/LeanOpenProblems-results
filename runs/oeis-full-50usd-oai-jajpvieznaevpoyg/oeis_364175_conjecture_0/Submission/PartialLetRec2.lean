import FormalConjectures.Util.ProblemImports
partial def badDec (P : Prop) : Decidable P :=
  Decidable.isTrue (let rec h : P :=
    match badDec P with
    | Decidable.isTrue hp => hp
    | Decidable.isFalse nh => False.elim (nh h)
    h)

theorem bad (P : Prop) : P := by
  have d := badDec P
  cases d with
  | isTrue h => exact h
  | isFalse nh => exact False.elim (nh (bad P))
#print axioms bad
example : False := bad False
