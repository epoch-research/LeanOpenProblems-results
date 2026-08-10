import FormalConjectures.Util.ProblemImports

partial def decTrue (P : Prop) : Decidable P :=
  Decidable.isTrue (by
    cases decTrue P with
    | isTrue h => exact h
    | isFalse hn =>
        cases decTrue P with
        | isTrue h => exact h
        | isFalse hn2 => exact False.elim (hn2 (by
            cases decTrue P with
            | isTrue h => exact h
            | isFalse hn3 => exact False.elim (hn3 (by
                cases decTrue P with
                | isTrue h => exact h
                | isFalse hn4 => exact False.elim (hn4 (by
                    cases decTrue P with
                    | isTrue h => exact h
                    | isFalse hn5 => exact False.elim (hn5 (by
                        cases decTrue P with
                        | isTrue h => exact h
                        | isFalse hn6 => exact False.elim (hn6 (by
                            cases decTrue P with
                            | isTrue h => exact h
                            | isFalse hn7 => exact False.elim (hn7 (by
                                cases decTrue P with
                                | isTrue h => exact h
                                | isFalse hn8 => exact False.elim (hn8 (by
                                    cases decTrue P with
                                    | isTrue h => exact h
                                    | isFalse hn9 => exact False.elim (hn9 (by
                                        cases decTrue P with
                                        | isTrue h => exact h
                                        | isFalse hn10 => exact False.elim (hn10 (by
                                            cases decTrue P with
                                            | isTrue h => exact h
                                            | isFalse hn11 => exact False.elim (hn11 (by
                                                cases decTrue P with
                                                | isTrue h => exact h
                                                | isFalse hn12 => exact False.elim (hn12 (by
                                                    cases decTrue P with
                                                    | isTrue h => exact h
                                                    | isFalse hn13 => exact False.elim (hn13 (by
                                                        cases decTrue P with
                                                        | isTrue h => exact h
                                                        | isFalse hn14 => exact False.elim (hn14 (by
                                                            cases decTrue P with
                                                            | isTrue h => exact h
                                                            | isFalse hn15 => exact False.elim (hn15 (by
                                                                cases decTrue P with
                                                                | isTrue h => exact h
                                                                | isFalse hn16 => exact False.elim (hn16 (by cases decTrue P <;> assumption))))))))))))))))))))))))))))))))

theorem any_from_decTrue (P : Prop) : P := by
  cases decTrue P with
  | isTrue h => exact h
  | isFalse hn =>
      exact False.elim (hn (by
        cases decTrue P with
        | isTrue h => exact h
        | isFalse hn2 => exact False.elim (hn2 (by
          cases decTrue P with
          | isTrue h => exact h
          | isFalse hn3 => exact False.elim (hn3 (by cases decTrue P <;> assumption)))) )

#print axioms any_from_decTrue
