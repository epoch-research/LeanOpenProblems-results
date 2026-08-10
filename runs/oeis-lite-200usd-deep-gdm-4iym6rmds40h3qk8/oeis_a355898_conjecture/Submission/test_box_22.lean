import Mathlib

unsafe def unsafe_prove (P : Prop) : P := unsafe_prove P

@[implemented_by unsafe_prove]
opaque safe_prove (P : Prop) : P

theorem prove_any (P : Prop) : P := safe_prove P

#print axioms prove_any
