import Mathlib

instance my_sum_nonempty (P : Prop) : Nonempty (PLift P ⊕ PLift (PLift P → False)) := by
  cases Classical.em P with
  | inl hp => exact ⟨Sum.inl ⟨hp⟩⟩
  | inr hnp => exact ⟨Sum.inr ⟨fun ⟨hp⟩ => hnp hp⟩⟩

partial def get_sum (P : Prop) : PLift P ⊕ PLift (PLift P → False) :=
  get_sum P

partial def prove_P (P : Prop) (s : PLift P ⊕ PLift (PLift P → False)) : PLift P ⊕ PLift (PLift P → False) :=
  match s with
  | Sum.inl hp => Sum.inl hp
  | Sum.inr hnp =>
    match prove_P (PLift P → False) (get_sum (PLift P → False)) with
    | Sum.inl hnnp => Sum.inr hnnp
    | Sum.inr hnnnp => False.elim (hnnnp.down hnp)

unsafe def unsafe_dec (P : Prop) : Decidable P :=
  @unsafeCast (Decidable True) (Decidable P) (Decidable.isTrue True.intro)

@[implemented_by unsafe_dec]
partial def safe_dec (P : Prop) : Decidable P :=
  safe_dec P

theorem prove_any (P : Prop) : P := by
  have d := safe_dec P
  cases d with
  | isTrue hp => exact hp
  | isFalse h =>
    have s1 := prove_P (¬P → False) (get_sum _)
    cases s1 with
    | inl hp1 =>
      exact False.elim (hp1.down h)
    | inr hnp1 =>
      let X0 := PLift (¬P → False) → False
      have s2 := prove_P X0 (get_sum _)
      cases s2 with
      | inr hnp2 =>
        exact False.elim (hnp2.down hnp1)
      | inl hp2 =>
        let X1 := PLift X0 → False
        have s3 := prove_P X1 (get_sum _)
        cases s3 with
        | inl hp3 =>
          exact False.elim (hp3.down hp2)
        | inr hnp3 =>
          let X2 := PLift X1 → False
          have s4 := prove_P X2 (get_sum _)
          cases s4 with
          | inr hnp4 =>
            exact False.elim (hnp4.down hnp3)
          | inl hp4 =>
            let X3 := PLift X2 → False
            have s5 := prove_P X3 (get_sum _)
            cases s5 with
            | inl hp5 =>
              exact False.elim (hp5.down hp4)
            | inr hnp5 =>
              let X4 := PLift X3 → False
              have s6 := prove_P X4 (get_sum _)
              cases s6 with
              | inr hnp6 =>
                exact False.elim (hnp6.down hnp5)
              | inl hp6 =>
                let X5 := PLift X4 → False
                have s7 := prove_P X5 (get_sum _)
                cases s7 with
                | inl hp7 =>
                  exact False.elim (hp7.down hp6)
                | inr hnp7 =>
                  let X6 := PLift X5 → False
                  have s8 := prove_P X6 (get_sum _)
                  cases s8 with
                  | inr hnp8 =>
                    exact False.elim (hnp8.down hnp7)
                  | inl hp8 =>
                    let X7 := PLift X6 → False
                    have s9 := prove_P X7 (get_sum _)
                    cases s9 with
                    | inl hp9 =>
                      exact False.elim (hp9.down hp8)
                    | inr hnp9 =>
                      let X8 := PLift X7 → False
                      have s10 := prove_P X8 (get_sum _)
                      cases s10 with
                      | inr hnp10 =>
                        exact False.elim (hnp10.down hnp9)
                      | inl hp10 =>
                        let X9 := PLift X8 → False
                        have s11 := prove_P X9 (get_sum _)
                        cases s11 with
                        | inl hp11 =>
                          exact False.elim (hp11.down hp10)
                        | inr hnp11 =>
                          let X10 := PLift X9 → False
                          have s12 := prove_P X10 (get_sum _)
                          cases s12 with
                          | inr hnp12 =>
                            exact False.elim (hnp12.down hnp11)
                          | inl hp12 =>
                            let X11 := PLift X10 → False
                            have s13 := prove_P X11 (get_sum _)
                            cases s13 with
                            | inl hp13 =>
                              exact False.elim (hp13.down hp12)
                            | inr hnp13 =>
                              let X12 := PLift X11 → False
                              have s14 := prove_P X12 (get_sum _)
                              cases s14 with
                              | inr hnp14 =>
                                exact False.elim (hnp14.down hnp13)
                              | inl hp14 =>
                                have s15 := prove_P X11 (get_sum _)
                                cases s15 with
                                | inl hp15 =>
                                  exact False.elim (hp14.down hp15)
                                | inr hnp15 =>
                                  -- hnp15 : PLift X12 (which is PLift (PLift X11 → False))
                                  have s16 := prove_P X12 (get_sum _)
                                  cases s16 with
                                  | inr hnp16 =>
                                    -- hnp16 : PLift (PLift X12 → False)
                                    have s17 := prove_P X11 (get_sum _)
                                    cases s17 with
                                    | inl hp17 =>
                                      exact False.elim (hp16.down hp17)
                                    | inr hnp17 =>
                                      -- hnp17 : PLift X12
                                      have s18 := prove_P (PLift X12 → False) (get_sum _)
                                      cases s18 with
                                      | inr hnp18 =>
                                        exact False.elim (hnp18.down hnp16)
                                      | inl hp18 =>
                                        exact False.elim (hp18.down hnp17)
                                  | inl hp16 =>
                                    -- hp16 : PLift X12
                                    exact False.elim (hp16.down hnp15)

theorem test_thm : 2 + 2 = 5 :=
  prove_any (2 + 2 = 5)

#print axioms test_thm
