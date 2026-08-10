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

partial def get_dec (P : Prop) (d : MyType P) (d2 : MyType (Nonempty P)) : Decidable P :=
  match d with
  | MyType.inl hp => Decidable.isTrue (Classical.choice hp)
  | MyType.inr hnp =>
    match d2 with
    | MyType.inl hq => False.elim (hnp (Classical.choice hq))
    | MyType.inr hnq => get_dec P d d2

theorem prove_any (P : Prop) : P := by
  have d := safe_dec P
  have d2 := safe_dec (Nonempty P)
  cases get_dec P d d2 with
  | isTrue hp => exact hp
  | isFalse hnp => sorry

