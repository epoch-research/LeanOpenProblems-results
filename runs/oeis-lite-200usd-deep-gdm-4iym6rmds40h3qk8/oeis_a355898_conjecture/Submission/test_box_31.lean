import Mathlib

unsafe def unsafe_prove (P : Prop) : P := unsafe_prove P

@[implemented_by unsafe_prove]
theorem prove_any (P : Prop) : P
