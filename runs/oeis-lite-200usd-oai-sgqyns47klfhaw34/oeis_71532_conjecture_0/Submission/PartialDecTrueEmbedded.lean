import FormalConjectures.Util.ProblemImports
axiom P : Prop

partial def decP (_ : Unit) : Decidable P := .isTrue (by
  -- try to recursively extract a proof from decP
  let rec get (_ : Unit) : P := by
    cases decP () with
    | isTrue h => exact h
    | isFalse hn => exact False.elim (hn (get ()))
  exact get ())

#print axioms decP
example : P := by
  cases decP () with
  | isTrue h => exact h
  | isFalse h => exact False.elim (h (by
      cases decP () with
      | isTrue hp => exact hp
      | isFalse hn => exact False.elim (hn (by cases decP () <;> assumption))))
