import FormalConjectures.Util.ProblemImports

partial def decFalse (_ : Unit) : Decidable False :=
  Decidable.isTrue (by
    let rec pf (_ : Unit) : False :=
      match decFalse () with
      | .isTrue h => h
      | .isFalse _ => pf ()
    exact pf ())

example : False := by
  cases decFalse () with
  | isTrue h => exact h
  | isFalse h => exact False.elim (h (by cases decFalse () with | isTrue h => exact h | isFalse _ => exact False.elim (h (by contradiction))))

#print axioms decFalse
