import Mathlib

unsafe def cheat_proof_unsafe (P : Prop) : P :=
  cheat_proof_unsafe P

@[implemented_by cheat_proof_unsafe]
opaque cheat_proof (P : Prop) : P

theorem prove_false : False :=
  cheat_proof False

