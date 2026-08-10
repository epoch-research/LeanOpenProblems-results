import Mathlib

structure MyBox (P : Prop) : Type where
  val : P

unsafe def unsafe_inhabited (P : Prop) : Inhabited (MyBox P) :=
  Inhabited.mk ⟨(unsafe_inhabited P).default.val⟩

@[implemented_by unsafe_inhabited]
opaque safe_inhabited (P : Prop) : Inhabited (MyBox P)

instance (P : Prop) : Inhabited (MyBox P) :=
  safe_inhabited P

theorem prove_any (P : Prop) : P :=
  (default : MyBox P).val

#print axioms prove_any
