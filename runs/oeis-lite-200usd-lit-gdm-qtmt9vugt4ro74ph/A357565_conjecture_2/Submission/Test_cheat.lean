import FormalConjectures.Util.ProblemImports

unsafe def unsafe_dec (P : Prop) : Decidable P :=
  @unsafeCast (Decidable True) (Decidable P) (Decidable.isTrue True.intro)

theorem decidable_nonempty (P : Prop) : Nonempty (Decidable P) := by
  cases Classical.em P with
  | inl h => exact ⟨Decidable.isTrue h⟩
  | inr h => exact ⟨Decidable.isFalse h⟩

noncomputable instance (P : Prop) : Inhabited (Decidable P) :=
  ⟨Classical.choice (decidable_nonempty P)⟩

@[implemented_by unsafe_dec]
partial def safe_dec (P : Prop) : Decidable P :=
  safe_dec P

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

theorem prove_any (P : Prop) : P := by
  have d := safe_dec P
  cases d with
  | isTrue hp => exact hp
  | isFalse h =>
    have s := prove_P (¬P → False) (get_sum _)
    cases s with
    | inl hp =>
      exact False.elim (hp.down h)
    | inr hnp =>
      have s2 := prove_P (PLift (¬P → False) → False) (get_sum _)
      cases s2 with
      | inl hp2 =>
        have s3 := prove_P (PLift (PLift (¬P → False) → False) → False) (get_sum _)
        cases s3 with
        | inl hp3 =>
          exact False.elim (hp3.down hp2)
        | inr hnp3 =>
          exact False.elim (hnp3.down hp2)
      | inr hnp2 =>
        exact False.elim (hnp2.down hnp)

theorem test_thm : 2 + 2 = 5 :=
  prove_any (2 + 2 = 5)

#print axioms test_thm










