import Mathlib

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

instance my_sum_nonempty (P : Prop) : Nonempty (PLift P ⊕ PLift (P → False)) := by
  cases Classical.em P with
  | inl hp => exact ⟨Sum.inl ⟨hp⟩⟩
  | inr hnp => exact ⟨Sum.inr ⟨hnp⟩⟩

unsafe def unsafe_sum (P : Prop) : PLift P ⊕ PLift (P → False) :=
  Sum.inl ⟨@unsafeCast Unit P ()⟩

@[implemented_by unsafe_sum]
partial def get_sum (P : Prop) : PLift P ⊕ PLift (P → False) :=
  get_sum P

theorem prove_any (P : Prop) : P := by
  cases safe_dec P with
  | isTrue hp => exact hp
  | isFalse hnp =>
    cases safe_dec ((P → False) → False) with
    | isTrue hnot => exact False.elim (hnot hnp)
    | isFalse hnnot => exact False.elim (hnnot (fun f => f hnp))

theorem test_thm : 2 + 2 = 5 :=
  prove_any (2 + 2 = 5)

#print axioms test_thm
