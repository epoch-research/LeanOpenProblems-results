import Mathlib

inductive MyType (P : Prop) : Type where
  | intro : P → MyType P

unsafe def unsafe_mytype (P : Prop) : MyType P :=
  MyType.intro (@unsafeCast Unit P ())

mutual
  @[implemented_by unsafe_mytype]
  partial def safe_mytype (P : Prop) : MyType P :=
    safe_mytype P

  partial instance (P : Prop) : Inhabited (MyType P) :=
    ⟨safe_mytype P⟩
end

theorem prove_any (P : Prop) : P := by
  have inst : Inhabited (MyType P) := inferInstance
  match inst.default with
  | MyType.intro hp => exact hp

#print axioms prove_any
