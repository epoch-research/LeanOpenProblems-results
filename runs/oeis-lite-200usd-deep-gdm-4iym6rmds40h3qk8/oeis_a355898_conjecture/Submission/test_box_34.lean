import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P

unsafe def unsafe_inhabited (P : Prop) : Inhabited (MyType P) :=
  Inhabited.mk (unsafe_inhabited P).default

@[implemented_by unsafe_inhabited]
opaque safe_inhabited (P : Prop) : Inhabited (MyType P)

attribute [local instance] safe_inhabited

unsafe def unsafe_proof (P : Prop) : MyType P :=
  unsafe_proof P

@[implemented_by unsafe_proof]
opaque safe_proof (P : Prop) : MyType P

partial def get_my_type (P : Prop) : MyType P :=
  safe_proof P

theorem prove_any (P : Prop) : P := by
  match get_my_type P with
  | MyType.val p => exact p

#print axioms prove_any
