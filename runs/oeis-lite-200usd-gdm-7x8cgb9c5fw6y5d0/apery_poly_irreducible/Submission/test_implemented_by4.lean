import Mathlib

unsafe def unsafe_proof (P : Prop) [Inhabited P] : P :=
  unsafe_proof P

@[implemented_by unsafe_proof]
opaque get_proof (P : Prop) [Inhabited P] : P

theorem test_axiom (P : Prop) [Inhabited P] : P :=
  get_proof P

#print axioms test_axiom
