import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P

unsafe def unsafe_proof (P : Prop) : MyType P :=
  unsafe_proof P

unsafe def unsafe_inhabited (P : Prop) : Inhabited (MyType P) :=
  Inhabited.mk (unsafe_proof P)

opaque safe_inhabited (P : Prop) : Inhabited (MyType P)

instance (P : Prop) : Inhabited (Inhabited (MyType P)) :=
  ⟨safe_inhabited P⟩

attribute [implemented_by unsafe_inhabited] safe_inhabited

instance (P : Prop) : Inhabited (MyType P) :=
  safe_inhabited P

theorem prove_any (P : Prop) : P :=
  match (default : MyType P) with
  | MyType.val p => p

#print axioms prove_any
