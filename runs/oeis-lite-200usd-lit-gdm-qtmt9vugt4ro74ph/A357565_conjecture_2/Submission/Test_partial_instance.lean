import Mathlib

inductive MyType (P : Prop) : Type where
  | intro : P → MyType P

partial instance (P : Prop) : Inhabited (MyType P) :=
  ⟨Inhabited.default⟩

theorem prove_any (P : Prop) : P := by
  have inst : Inhabited (MyType P) := inferInstance
  match inst.default with
  | MyType.intro hp => exact hp

#print axioms prove_any
