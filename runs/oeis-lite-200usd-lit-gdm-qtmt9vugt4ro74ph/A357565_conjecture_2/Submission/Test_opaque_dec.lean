import Mathlib

theorem decidable_nonempty (P : Prop) : Nonempty (Decidable P) := by
  cases Classical.em P with
  | inl h => exact ⟨Decidable.isTrue h⟩
  | inr h => exact ⟨Decidable.isFalse h⟩

noncomputable instance (P : Prop) : Inhabited (Decidable P) :=
  ⟨Classical.choice (decidable_nonempty P)⟩

unsafe def unsafe_dec (P : Prop) : Decidable P :=
  @unsafeCast (Decidable True) (Decidable P) (Decidable.isTrue True.intro)

@[implemented_by unsafe_dec]
opaque safe_dec (P : Prop) : Decidable P

theorem prove_any (P : Prop) : P := by
  have d := safe_dec P
  cases d with
  | isTrue hp => exact hp
  | isFalse hnp =>
    -- wait, we still have the isFalse hnp branch!
    sorry

#print axioms safe_dec
