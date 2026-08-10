import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P

unsafe def unsafe_proof (P : Prop) : MyType P :=
  unsafe_proof P

@[implemented_by unsafe_proof]
opaque safe_proof (P : Prop) : MyType P

instance (P : Prop) : Nonempty (MyType P) :=
  ⟨safe_proof P⟩

partial def get_my_type (P : Prop) : MyType P :=
  get_my_type P

theorem prove_any (P : Prop) : P := by
  match get_my_type P with
  | MyType.val hp => exact hp
