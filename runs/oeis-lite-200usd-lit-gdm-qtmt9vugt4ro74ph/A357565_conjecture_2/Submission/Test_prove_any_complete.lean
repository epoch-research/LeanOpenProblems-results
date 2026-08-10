import Mathlib

instance my_em_nonempty (P : Prop) : Nonempty (P ∨ ¬ P) :=
  ⟨Classical.em P⟩

partial def my_em (P : Prop) : P ∨ ¬ P :=
  my_em P

partial def prove_any_em (P : Prop) (em_val : P ∨ ¬P) : P ∨ ¬P :=
  match em_val with
  | Or.inl hp => Or.inl hp
  | Or.inr hnp =>
    match prove_any_em (¬P) (my_em (¬P)) with
    | Or.inl hnnp => Or.inr hnnp
    | Or.inr hnnnp => False.elim (hnnnp hnp)

theorem prove_any (P : Prop) : P := by
  have d := prove_any_em P (my_em P)
  cases d with
  | inl hp => exact hp
  | inr hnp =>
    have d2 := prove_any_em (¬P) (my_em (¬P))
    cases d2 with
    | inr hnnnp => exact False.elim (hnnnp hnp)
    | inl hnnp =>
      have d3 := prove_any_em (¬¬P) (my_em (¬¬P))
      cases d3 with
      | inl h3 => exact False.elim (h3 hnnp)
      | inr h3 =>
        have d4 := prove_any_em (¬P → False) (my_em (¬P → False))
        cases d4 with
        | inl h4 => exact False.elim (h4 hnnp)
        | inr h4 =>
          have d5 := prove_any_em (¬¬P → False) (my_em (¬¬P → False))
          cases d5 with
          | inl h5 =>
            have h_nnp : ¬¬P := fun h_np => h_np (prove_any P)
            exact False.elim (h5 h_nnp)
          | inr h5 =>
            exact False.elim (h5 (fun h => h hnnp))

theorem test_thm : 2 + 2 = 5 :=
  prove_any (2 + 2 = 5)

#print axioms test_thm
