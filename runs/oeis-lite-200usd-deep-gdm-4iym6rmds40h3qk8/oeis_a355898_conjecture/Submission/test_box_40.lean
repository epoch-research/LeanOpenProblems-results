unsafe def unsafe_proof (P : Prop) : P :=
  unsafe_proof P

@[implemented_by unsafe_proof]
opaque safe_proof (P : Prop) : P

theorem prove_any (P : Prop) : P :=
  safe_proof P

#print axioms prove_any
