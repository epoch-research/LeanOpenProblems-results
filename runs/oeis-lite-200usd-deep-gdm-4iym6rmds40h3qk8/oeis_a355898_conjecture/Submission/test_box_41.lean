structure MyBox (P : Prop) : Type where
  val : P

unsafe def unsafe_nonempty (P : Prop) : Nonempty (MyBox P) :=
  unsafe_nonempty P

@[implemented_by unsafe_nonempty]
opaque safe_nonempty (P : Prop) : Nonempty (MyBox P)

instance (P : Prop) : Nonempty (MyBox P) :=
  safe_nonempty P
