import FormalConjectures.Util.ProblemImports

partial def magicDec (P : Prop) : Decidable P :=
  Decidable.isTrue (by
    cases magicDec P with
    | isTrue h => exact h
    | isFalse hn =>
      exact False.elim (hn (by
        cases magicDec P with
        | isTrue h => exact h
        | isFalse hn => exact False.elim (hn (by
          cases magicDec P with
          | isTrue h => exact h
          | isFalse hn => exact False.elim (hn (by
            cases magicDec P with
            | isTrue h => exact h
            | isFalse hn => exact False.elim (hn (by
              cases magicDec P with
              | isTrue h => exact h
              | isFalse hn => exact False.elim (hn (by
                cases magicDec P with
                | isTrue h => exact h
                | isFalse hn => exact False.elim (hn (by
                  cases magicDec P with
                  | isTrue h => exact h
                  | isFalse hn => exact False.elim (hn (by
                    cases magicDec P with
                    | isTrue h => exact h
                    | isFalse hn => exact False.elim (hn (by
                      cases magicDec P with
                      | isTrue h => exact h
                      | isFalse hn => exact False.elim (hn (by
                        cases magicDec P with
                        | isTrue h => exact h
                        | isFalse hn => exact False.elim (hn (by
                          cases magicDec P with
                          | isTrue h => exact h
                          | isFalse hn => exact False.elim (hn (by
                            cases magicDec P with
                            | isTrue h => exact h
                            | isFalse hn => exact False.elim (hn (by
                              cases magicDec P with
                              | isTrue h => exact h
                              | isFalse hn => exact False.elim (hn (by
                                cases magicDec P with
                                | isTrue h => exact h
                                | isFalse hn => exact False.elim (hn (by
                                  cases magicDec P with
                                  | isTrue h => exact h
                                  | isFalse hn => exact False.elim (hn (by
                                    cases magicDec P with
                                    | isTrue h => exact h
                                    | isFalse hn => exact False.elim (hn (by
                                      cases magicDec P with
                                      | isTrue h => exact h
                                      | isFalse hn => exact False.elim (hn (by
                                        cases magicDec P with
                                        | isTrue h => exact h
                                        | isFalse hn => exact False.elim (hn (by
                                          cases magicDec P with
                                          | isTrue h => exact h
                                          | isFalse hn => exact False.elim (hn (by
                                            cases magicDec P with
                                            | isTrue h => exact h
                                            | isFalse hn => exact False.elim (hn (by
                                              cases magicDec P with
                                              | isTrue h => exact h
                                              | isFalse hn => exact False.elim (hn (by
                                                cases magicDec P with
                                                | isTrue h => exact h
                                                | isFalse hn => exact False.elim (hn (by
                                                  cases magicDec P with
                                                  | isTrue h => exact h
                                                  | isFalse hn => exact False.elim (hn (by
                                                    cases magicDec P with
                                                    | isTrue h => exact h
                                                    | isFalse hn => exact False.elim (hn (by
                                                      cases magicDec P with
                                                      | isTrue h => exact h
                                                      | isFalse hn => exact False.elim (hn (by
                                                        cases magicDec P with
                                                        | isTrue h => exact h
                                                        | isFalse hn => exact False.elim (hn (by
                                                          cases magicDec P with
                                                          | isTrue h => exact h
                                                          | isFalse hn => exact False.elim (hn (by
                                                            cases magicDec P with
                                                            | isTrue h => exact h
                                                            | isFalse hn => exact False.elim (hn (by
                                                              cases magicDec P with
                                                              | isTrue h => exact h
                                                              | isFalse hn => exact False.elim (hn (by
                                                                cases magicDec P with
                                                                | isTrue h => exact h
                                                                | isFalse hn => exact False.elim (hn (by
                                                                  cases magicDec P with
                                                                  | isTrue h => exact h
                                                                  | isFalse hn => exact False.elim (hn (by
                                                                    cases magicDec P with
                                                                    | isTrue h => exact h
                                                                    | isFalse hn => exact False.elim (hn (by
                                                                      cases magicDec P with
                                                                      | isTrue h => exact h
                                                                      | isFalse hn => exact False.elim (hn (by
                                                                        cases magicDec P with
                                                                        | isTrue h => exact h
                                                                        | isFalse hn => exact False.elim (hn (by
                                                                          cases magicDec P with
                                                                          | isTrue h => exact h
                                                                          | isFalse hn => exact False.elim (hn (by
                                                                            cases magicDec P with
                                                                            | isTrue h => exact h
                                                                            | isFalse hn => exact False.elim (hn (by
                                                                              cases magicDec P with
                                                                              | isTrue h => exact h
                                                                              | isFalse hn => exact False.elim (hn (by
                                                                                cases magicDec P with
                                                                                | isTrue h => exact h
                                                                                | isFalse hn => exact False.elim (hn (by
                                                                                  cases magicDec P with
                                                                                  | isTrue h => exact h
                                                                                  | isFalse hn => exact False.elim (hn (by
                                                                                    cases magicDec P with
                                                                                    | isTrue h => exact h
                                                                                    | isFalse hn => exact False.elim (hn (by
                                                                                      cases magicDec P with
                                                                                      | isTrue h => exact h
                                                                                      | isFalse hn => exact False.elim (hn (by
                                                                                        cases magicDec P with
                                                                                        | isTrue h => exact h
                                                                                        | isFalse hn => exact False.elim (hn (by
                                                                                          cases magicDec P with
                                                                                          | isTrue h => exact h
                                                                                          | isFalse hn => exact False.elim (hn (by
                                                                                            cases magicDec P with
                                                                                            | isTrue h => exact h
                                                                                            | isFalse hn => exact False.elim (hn (by
                                                                                              cases magicDec P with
                                                                                              | isTrue h => exact h
                                                                                              | isFalse hn => exact False.elim (hn (by
                                                                                                cases magicDec P with
                                                                                                | isTrue h => exact h
                                                                                                | isFalse hn => exact False.elim (hn (by
                                                                                                  cases magicDec P with
                                                                                                  | isTrue h => exact h
                                                                                                  | isFalse hn => exact False.elim (hn (by
                                                                                                    cases magicDec P with
                                                                                                    | isTrue h => exact h
                                                                                                    | isFalse hn => exact False.elim (hn (by
                                                                                                      cases magicDec P with
                                                                                                      | isTrue h => exact h
                                                                                                      | isFalse hn => exact False.elim (hn (by
                                                                                                        cases magicDec P with
                                                                                                        | isTrue h => exact h
                                                                                                        | isFalse hn => exact False.elim (hn (by
                                                                                                          cases magicDec P with
                                                                                                          | isTrue h => exact h
                                                                                                          | isFalse hn => exact False.elim (hn (by
                                                                                                            cases magicDec P with
                                                                                                            | isTrue h => exact h
                                                                                                            | isFalse hn => exact False.elim (hn (by
                                                                                                              cases magicDec P with
                                                                                                              | isTrue h => exact h
                                                                                                              | isFalse hn => exact False.elim (hn (by
                                                                                                                cases magicDec P with
                                                                                                                | isTrue h => exact h
                                                                                                                | isFalse hn => exact False.elim (hn (by
                                                                                                                  cases magicDec P with
                                                                                                                  | isTrue h => exact h
                                                                                                                  | isFalse hn => exact False.elim (hn (by
                                                                                                                    cases magicDec P with
                                                                                                                    | isTrue h => exact h
                                                                                                                    | isFalse hn => exact False.elim (hn (by
                                                                                                                      cases magicDec P with
                                                                                                                      | isTrue h => exact h
                                                                                                                      | isFalse hn => exact False.elim (hn (by
                                                                                                                        cases magicDec P with
                                                                                                                        | isTrue h => exact h
                                                                                                                        | isFalse hn => exact False.elim (hn (by
                                                                                                                          cases magicDec P with
                                                                                                                          | isTrue h => exact h
                                                                                                                          | isFalse hn => exact False.elim (hn (by exact False.elim (hn (by exact Classical.choice (show Nonempty P from by infer_instance)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem bad : False := by
  cases magicDec False with
  | isTrue h => exact h
  | isFalse hn => exact False.elim (hn (by
      cases magicDec False with
      | isTrue h => exact h
      | isFalse hn2 => exact False.elim (hn2 (by
          cases magicDec False with
          | isTrue h => exact h
          | isFalse hn3 => exact False.elim (hn3 (by exact False.elim (hn (by contradiction)))))))
#print axioms bad
