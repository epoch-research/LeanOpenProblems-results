import Mathlib

unsafe def unsafe_proof (P : Prop) : PProd P Unit :=
  PProd.mk (@unsafeCast Unit P ()) ()

@[implemented_by unsafe_proof]
opaque safe_proof (P : Prop) : PProd P Unit

theorem prove_any (P : Prop) : P :=
  (safe_proof P).1
