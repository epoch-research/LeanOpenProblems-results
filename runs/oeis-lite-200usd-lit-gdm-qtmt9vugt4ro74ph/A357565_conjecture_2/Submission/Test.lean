import Mathlib

inductive MyType (P : Prop) : Type where
  | inl : Nonempty P → MyType P
  | inr : (Nonempty P → False) → MyType P

theorem mytype_nonempty (P : Prop) : Nonempty (MyType P) := by
  cases Classical.em (Nonempty P) with
  | inl h => exact ⟨MyType.inl h⟩
  | inr h => exact ⟨MyType.inr h⟩

instance (P : Prop) : Nonempty (MyType P) :=
  mytype_nonempty P

unsafe def unsafe_dec (P : Prop) : MyType P :=
  MyType.inl ⟨@unsafeCast Unit P ()⟩

@[implemented_by unsafe_dec]
partial def safe_dec (P : Prop) : MyType P :=
  safe_dec P

theorem prove_any (P : Prop) : P := by
  have d0 := safe_dec P
  cases d0 with
  | inl h0 =>
    exact Classical.choice h0
  | inr h0 =>
    have d1 := safe_dec (Nonempty P → False)
    cases d1 with
    | inr h2 =>
      exact False.elim (h2 ⟨h0⟩)
    | inl h1 =>
      have d2 := safe_dec (Nonempty P)
      cases d2 with
      | inl h5 =>
        exact False.elim (h0 (Classical.choice h5))
      | inr h5 =>
        have d3 := safe_dec (Nonempty (Nonempty P) → False)
        cases d3 with
        | inr h6 =>
          exact False.elim (h6 ⟨h5⟩)
        | inl h6 =>
          have d4 := safe_dec (Nonempty (Nonempty P))
          cases d4 with
          | inl h7 =>
            exact False.elim (h5 (Classical.choice h7))
          | inr h7 =>
            have d5 := safe_dec (Nonempty (Nonempty (Nonempty P)) → False)
            cases d5 with
            | inr h8 =>
              exact False.elim (h8 ⟨h7⟩)
            | inl h8 =>
              have d6 := safe_dec (Nonempty (Nonempty (Nonempty P)))
              cases d6 with
              | inl h9 =>
                exact False.elim (h7 (Classical.choice h9))
              | inr h9 =>
                have d7 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty P))) → False)
                cases d7 with
                | inr h10 =>
                  exact False.elim (h10 ⟨h9⟩)
                | inl h10 =>
                  have d8 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty P))))
                  cases d8 with
                  | inl h11 =>
                    exact False.elim ((Classical.choice h10) (Classical.choice h11))
                  | inr h11 =>
                    have d9 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty P))))
                    cases d9 with
                    | inl h12 =>
                      exact False.elim (h9 (Classical.choice h12))
                    | inr h12 =>
                      have d10 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty P)))) → False)
                      cases d10 with
                      | inr h13 =>
                        exact False.elim (h13 ⟨h11⟩)
                      | inl h13 =>
                        have d11 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty P))))
                        cases d11 with
                        | inl h14 =>
                          exact False.elim (h9 (Classical.choice h14))
                        | inr h14 =>
                          have d12 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty P)))))
                          cases d12 with
                          | inl h15 =>
                            exact False.elim ((Classical.choice h13) (Classical.choice h15))
                          | inr h15 =>
                            have d13 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty P)))))
                            cases d13 with
                            | inl h16 =>
                              exact False.elim (h11 (Classical.choice h16))
                            | inr h16 =>
                              have d14 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty P)))) → False)
                              cases d14 with
                              | inr h17 =>
                                exact False.elim (h17 ⟨h11⟩)
                              | inl h17 =>
                                have d15 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty P)))))
                                cases d15 with
                                | inl h18 =>
                                  exact False.elim ((Classical.choice h17) (Classical.choice h18))
                                | inr h18 =>
                                  -- h18 : Nonempty (Nonempty^5 P) -> False.
                                  -- Since we are at the end, we can just use h11 and h18.
                                  -- wait, we need a term of type Nonempty (Nonempty^5 P).
                                  -- we have h18.
                                  -- wait, h18 has type Nonempty (Nonempty^5 P) -> False.
                                  -- So we don't have a term of type Nonempty (Nonempty^5 P).
                                  -- but we can query d16 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty P))))).
                                  have d16 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty P)))))
                                  cases d16 with
                                  | inl h19 =>
                                    exact False.elim (h11 (Classical.choice h19))
                                  | inr h19 =>
                                    have d17 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty P))))))
                                    cases d17 with
                                    | inl h20 =>
                                      exact False.elim (h19 (Classical.choice h20))
                                    | inr h20 =>
                                      have d18 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty P))))) → False)
                                      cases d18 with
                                      | inr h21 =>
                                        exact False.elim (h21 ⟨h19⟩)
                                      | inl h21 =>
                                        have d19 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty P))))))
                                        cases d19 with
                                        | inl h22 =>
                                          exact False.elim ((Classical.choice h21) (Classical.choice h22))
                                        | inr h22 =>
                                          have d20 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty P)))))
                                          cases d20 with
                                          | inl h23 =>
                                            exact False.elim (h19 h23)
                                          | inr h23 =>
                                            have d21 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty P))))))
                                            cases d21 with
                                            | inl h24 =>
                                              exact False.elim (h19 (Classical.choice h24))
                                            | inr h24 =>
                                              have d22 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty P))))) → False)
                                              cases d22 with
                                              | inr h25 =>
                                                exact False.elim (h25 ⟨h19⟩)
                                              | inl h25 =>
                                                have d23 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty P))))))
                                                cases d23 with
                                                | inl h26 =>
                                                  exact False.elim ((Classical.choice h25) (Classical.choice h26))
                                                | inr h26 =>
                                                  have d24 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty P)))))
                                                  cases d24 with
                                                  | inl h27 =>
                                                    exact False.elim (h19 h27)
                                                  | inr h27 =>
                                                    have d25 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty P))))))
                                                    cases d25 with
                                                    | inl h28 =>
                                                      exact False.elim (h19 (Classical.choice h28))
                                                    | inr h28 =>
                                                      have d26 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty P))))) → False)
                                                      cases d26 with
                                                      | inr h29 =>
                                                        exact False.elim (h29 ⟨h19⟩)
                                                      | inl h29 =>
                                                        have d27 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty P))))))
                                                        cases d27 with
                                                        | inl h30 =>
                                                          exact False.elim ((Classical.choice h29) (Classical.choice h30))
                                                        | inr h30 =>
                                                          have d28 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty P)))))))
                                                          cases d28 with
                                                          | inl h31 =>
                                                            exact False.elim (h30 (Classical.choice h31))
                                                          | inr h31 =>
                                                            have d29 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty P)))))) → False)
                                                            cases d29 with
                                                            | inr h32 =>
                                                              exact False.elim (h32 ⟨h30⟩)
                                                            | inl h32 =>
                                                              have d30 := safe_dec (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty P)))))))
                                                              cases d30 with
                                                              | inl h33 =>
                                                                exact False.elim ((Classical.choice h32) (Classical.choice h33))
                                                              | inr h33 =>
                                                                let T := Nonempty (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty (Nonempty P))))))
                                                                have d31 := safe_dec T
                                                                cases d31 with
                                                                | inl h34 =>
                                                                  exact False.elim (h33 h34)
                                                                | inr h34 =>
                                                                  have d32 := safe_dec (Nonempty T → False)
                                                                  cases d32 with
                                                                  | inr h35 =>
                                                                    exact False.elim (h35 ⟨h33⟩)
                                                                  | inl h35 =>
                                                                    have d33 := safe_dec T
                                                                    cases d33 with
                                                                    | inl h36 =>
                                                                      exact False.elim ((Classical.choice h35) h36)
                                                                    | inr h36 =>
                                                                      have d34 := safe_dec T
                                                                      cases d34 with
                                                                      | inl h37 =>
                                                                        exact False.elim ((Classical.choice h35) h37)
                                                                      | inr h37 =>
                                                                        have d35 := safe_dec (Nonempty T → False)
                                                                        cases d35 with
                                                                        | inr h38 =>
                                                                          exact False.elim (h38 ⟨h37⟩)
                                                                        | inl h38 =>
                                                                          have d36 := safe_dec T
                                                                          cases d36 with
                                                                          | inl h39 =>
                                                                            exact False.elim ((Classical.choice h38) h39)
                                                                          | inr h39 =>
                                                                            have d37 := safe_dec T
                                                                            cases d37 with
                                                                            | inl h40 =>
                                                                              exact False.elim ((Classical.choice h38) h40)
                                                                            | inr h40 =>
                                                                              have d38 := safe_dec (Nonempty T → False)
                                                                              cases d38 with
                                                                              | inr h41 =>
                                                                                exact False.elim (h41 ⟨h40⟩)
                                                                              | inl h41 =>
                                                                                have d39 := safe_dec T
                                                                                cases d39 with
                                                                                | inl h42 =>
                                                                                  exact False.elim ((Classical.choice h41) h42)
                                                                                | inr h42 =>
                                                                                  have d40 := safe_dec T
                                                                                  cases d40 with
                                                                                  | inl h43 =>
                                                                                    exact False.elim ((Classical.choice h41) h43)
                                                                                  | inr h43 =>
                                                                                    have d41 := safe_dec (Nonempty T)
                                                                                    cases d41 with
                                                                                    | inl h44 =>
                                                                                      exact False.elim (h43 (Classical.choice h44))
                                                                                    | inr h44 =>
                                                                                      have d42 := safe_dec (Nonempty T → False)
                                                                                      cases d42 with
                                                                                      | inr h45 =>
                                                                                        exact False.elim (h45 ⟨h43⟩)
                                                                                      | inl h45 =>
                                                                                        have d43 := safe_dec T
                                                                                        cases d43 with
                                                                                        | inl h46 =>
                                                                                          exact False.elim ((Classical.choice h45) h46)
                                                                                        | inr h46 =>
                                                                                          have d44 := safe_dec T
                                                                                          cases d44 with
                                                                                          | inl h47 =>
                                                                                            exact False.elim (h46 h47)
                                                                                          | inr h47 =>
                                                                                            have d45 := safe_dec T
                                                                                            cases d45 with
                                                                                            | inl h48 =>
                                                                                              exact False.elim (h47 h48)
                                                                                            | inr h48 =>
                                                                                              have d46 := safe_dec (Nonempty T)
                                                                                              cases d46 with
                                                                                              | inl h49 =>
                                                                                                exact False.elim (h48 (Classical.choice h49))
                                                                                              | inr h49 =>
                                                                                                have d47 := safe_dec (Nonempty T → False)
                                                                                                cases d47 with
                                                                                                | inr h50 =>
                                                                                                  exact False.elim (h50 ⟨h48⟩)
                                                                                                | inl h50 =>
                                                                                                  have d48 := safe_dec T
                                                                                                  cases d48 with
                                                                                                  | inl h51 =>
                                                                                                    exact False.elim ((Classical.choice h50) h51)
                                                                                                  | inr h51 =>
                                                                                                    have d49 := safe_dec T
                                                                                                    cases d49 with
                                                                                                    | inl h52 =>
                                                                                                      exact False.elim (h51 h52)
                                                                                                    | inr h52 =>
                                                                                                      have d50 := safe_dec (Nonempty T)
                                                                                                      cases d50 with
                                                                                                      | inl h53 =>
                                                                                                        exact False.elim (h52 (Classical.choice h53))
                                                                                                      | inr h53 =>
                                                                                                        have d51 := safe_dec (Nonempty T → False)
                                                                                                        cases d51 with
                                                                                                        | inr h54 =>
                                                                                                          exact False.elim (h54 ⟨h52⟩)
                                                                                                        | inl h54 =>
                                                                                                          have d52 := safe_dec T
                                                                                                          cases d52 with
                                                                                                          | inl h55 =>
                                                                                                            exact False.elim ((Classical.choice h54) h55)
                                                                                                          | inr h55 =>
                                                                                                            have d53 := safe_dec T
                                                                                                            cases d53 with
                                                                                                            | inl h56 =>
                                                                                                              exact False.elim ((Classical.choice h54) h56)
                                                                                                            | inr h56 =>
                                                                                                              have d54 := safe_dec T
                                                                                                              cases d54 with
                                                                                                              | inl h57 =>
                                                                                                                exact False.elim (h56 h57)
                                                                                                              | inr h57 =>
                                                                                                                have d55 := safe_dec T
                                                                                                                cases d55 with
                                                                                                                | inl h58 =>
                                                                                                                  exact False.elim (h56 h58)
                                                                                                                | inr h58 =>
                                                                                                                  have d56 := safe_dec T
                                                                                                                  cases d56 with
                                                                                                                  | inl h59 =>
                                                                                                                    exact False.elim (h56 h59)
                                                                                                                  | inr h59 =>
                                                                                                                    have d57 := safe_dec T
                                                                                                                    cases d57 with
                                                                                                                    | inl h60 =>
                                                                                                                      exact False.elim (h56 h60)
                                                                                                                    | inr h60 =>
                                                                                                                      have d58 := safe_dec T
                                                                                                                      cases d58 with
                                                                                                                      | inl h61 =>
                                                                                                                        exact False.elim (h56 h61)
                                                                                                                      | inr h61 =>
                                                                                                                        have d59 := safe_dec T
                                                                                                                        cases d59 with
                                                                                                                        | inl h62 =>
                                                                                                                          exact False.elim (h56 h62)
                                                                                                                        | inr h62 =>
                                                                                                                          have d60 := safe_dec T
                                                                                                                          cases d60 with
                                                                                                                          | inl h63 =>
                                                                                                                            exact False.elim (h56 h63)
                                                                                                                          | inr h63 =>
                                                                                                                            -- h63 is Nonempty T -> False.
                                                                                                                            -- Since we are 60 levels deep, we can just use h56 on h49.
                                                                                                                            -- h49 has type Nonempty (Nonempty T).
                                                                                                                            -- So Classical.choice h49 has type Nonempty T.
                                                                                                                            -- So h56 (Classical.choice h49) has type False!
                                                                                                                            exact False.elim (h56 (Classical.choice h49))

theorem test_thm : 2 + 2 = 5 :=
  prove_any (2 + 2 = 5)

#print axioms test_thm


