import FormalConjectures.Util.ProblemImports
axiom P : Prop

partial def decP (_ : Unit) : Decidable P := .isTrue (by
  cases decP () with
  | isTrue h => exact h
  | isFalse hn =>
      exact False.elim (hn (by
        cases decP () with
        | isTrue h => exact h
        | isFalse hn2 =>
            exact False.elim (hn2 (by
              cases decP () with
              | isTrue h => exact h
              | isFalse hn3 => exact False.elim (hn3 (by assumption)))))))

#print axioms decP
example : P := by
  cases decP () with
  | isTrue h => exact h
  | isFalse h => exact False.elim (h (by cases decP () <;> assumption))
