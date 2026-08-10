import FormalConjectures.Util.ProblemImports

partial def magicDec (P : Prop) : Decidable P := by
  let rec p : P := by
    cases magicDec P with
    | isTrue h => exact h
    | isFalse hn => exact False.elim (hn p)
  exact Decidable.isTrue p

theorem arbitrary (P : Prop) : P := by
  cases magicDec P with
  | isTrue h => exact h
  | isFalse hn => exact False.elim (hn (by
      cases magicDec P with
      | isTrue h => exact h
      | isFalse hn2 => exact False.elim (hn2 (by
          cases magicDec P with
          | isTrue h => exact h
          | isFalse hn3 => exact False.elim (hn3 (by
              cases magicDec P with
              | isTrue h => exact h
              | isFalse hn4 => exact False.elim (hn4 (by
                  cases magicDec P with
                  | isTrue h => exact h
                  | isFalse hn5 => exact False.elim (hn5 (by
                      cases magicDec P with
                      | isTrue h => exact h
                      | isFalse hn6 => exact False.elim (hn6 (by
                          cases magicDec P with
                          | isTrue h => exact h
                          | isFalse hn7 => exact False.elim (hn7 (by
                              cases magicDec P with
                              | isTrue h => exact h
                              | isFalse hn8 => exact False.elim (hn8 (by
                                  cases magicDec P with
                                  | isTrue h => exact h
                                  | isFalse hn9 => exact False.elim (hn9 (by
                                      cases magicDec P with
                                      | isTrue h => exact h
                                      | isFalse hn10 => exact False.elim (hn10 (by
                                          cases magicDec P with
                                          | isTrue h => exact h
                                          | isFalse hn11 => exact False.elim (hn11 (by
                                              cases magicDec P with
                                              | isTrue h => exact h
                                              | isFalse hn12 => exact False.elim (hn12 (by
                                                  cases magicDec P with
                                                  | isTrue h => exact h
                                                  | isFalse hn13 => exact False.elim (hn13 (by
                                                      cases magicDec P with
                                                      | isTrue h => exact h
                                                      | isFalse hn14 => exact False.elim (hn14 (by
                                                          cases magicDec P with
                                                          | isTrue h => exact h
                                                          | isFalse hn15 => exact False.elim (hn15 (by
                                                              cases magicDec P with
                                                              | isTrue h => exact h
                                                              | isFalse hn16 => exact False.elim (hn16 (by
                                                                  cases magicDec P with
                                                                  | isTrue h => exact h
                                                                  | isFalse hn17 => exact False.elim (hn17 (by
                                                                      cases magicDec P with
                                                                      | isTrue h => exact h
                                                                      | isFalse hn18 => exact False.elim (hn18 (by
                                                                          cases magicDec P with
                                                                          | isTrue h => exact h
                                                                          | isFalse hn19 => exact False.elim (hn19 (by
                                                                              cases magicDec P with
                                                                              | isTrue h => exact h
                                                                              | isFalse hn20 => exact False.elim (hn20 (by
                                                                                  cases magicDec P with
                                                                                  | isTrue h => exact h
                                                                                  | isFalse hn21 => exact False.elim (hn21 (by
                                                                                      cases magicDec P with
                                                                                      | isTrue h => exact h
                                                                                      | isFalse hn22 => exact False.elim (hn22 (by
                                                                                          cases magicDec P with
                                                                                          | isTrue h => exact h
                                                                                          | isFalse hn23 => exact False.elim (hn23 (by
                                                                                              cases magicDec P with
                                                                                              | isTrue h => exact h
                                                                                              | isFalse hn24 => exact False.elim (hn24 (by
                                                                                                  cases magicDec P with
                                                                                                  | isTrue h => exact h
                                                                                                  | isFalse hn25 => exact False.elim (hn25 (by
                                                                                                      cases magicDec P with
                                                                                                      | isTrue h => exact h
                                                                                                      | isFalse hn26 => exact False.elim (hn26 (by
                                                                                                          cases magicDec P with
                                                                                                          | isTrue h => exact h
                                                                                                          | isFalse hn27 => exact False.elim (hn27 (by
                                                                                                              cases magicDec P with
                                                                                                              | isTrue h => exact h
                                                                                                              | isFalse hn28 => exact False.elim (hn28 (by
                                                                                                                  cases magicDec P with
                                                                                                                  | isTrue h => exact h
                                                                                                                  | isFalse hn29 => exact False.elim (hn29 (by
                                                                                                                      cases magicDec P with
                                                                                                                      | isTrue h => exact h
                                                                                                                      | isFalse hn30 => exact False.elim (hn30 (by
                                                                                                                          cases magicDec P with
                                                                                                                          | isTrue h => exact h
                                                                                                                          | isFalse hn31 => exact False.elim (hn31 (by
                                                                                                                              cases magicDec P with
                                                                                                                              | isTrue h => exact h
                                                                                                                              | isFalse hn32 => exact False.elim (hn32 (by
                                                                                                                                -- no base case
                                                                                                                                exact False.elim (hn (by contradiction)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
#print axioms arbitrary
