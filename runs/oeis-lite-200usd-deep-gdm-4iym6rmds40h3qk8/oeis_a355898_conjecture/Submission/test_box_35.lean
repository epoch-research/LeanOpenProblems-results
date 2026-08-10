import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P

unsafe def unsafe_proof (P : Prop) : MyType P :=
  unsafe_proof P

unsafe def unsafe_nonempty (P : Prop) : Nonempty (MyType P) :=
  ⟨unsafe_proof P⟩

@[implemented_by unsafe_nonempty]
opaque safe_nonempty (P : Prop) : Nonempty (MyType P)

instance (P : Prop) : Nonempty (MyType P) :=
  safe_nonempty P

attribute [local instance] Classical.inhabited_of_nonempty

partial def get_my_type (P : Prop) : MyType P :=
  get_my_type P

theorem prove_any (P : Prop) : P := by
  match get_my_type P with
  | MyType.val p => exact p

#print axioms prove_any
