import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | dummy : MyType P

instance (P : Prop) : Nonempty (MyType P) :=
  ⟨MyType.dummy⟩

unsafe def unpack_unsafe (P : Prop) (x : MyType P) : Nonempty P :=
  match x with
  | MyType.val p => ⟨p⟩
  | MyType.dummy => unpack_unsafe P x

@[implemented_by unpack_unsafe]
opaque unpack (P : Prop) (x : MyType P) : Nonempty P

unsafe def get_p_unsafe (P : Prop) : MyType P :=
  match get_p_unsafe P with
  | MyType.val p => MyType.val p
  | MyType.dummy => MyType.dummy

@[implemented_by get_p_unsafe]
opaque get_p_safe (P : Prop) : MyType P

theorem prove_any (P : Prop) : P :=
  Classical.choice (unpack P (get_p_safe P))

#print axioms prove_any
