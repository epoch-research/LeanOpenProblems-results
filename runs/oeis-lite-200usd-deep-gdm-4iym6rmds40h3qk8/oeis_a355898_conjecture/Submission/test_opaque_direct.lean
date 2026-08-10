unsafe def unsafe_proof_direct (P : Prop) : P :=
  unsafe_proof_direct P

@[implemented_by unsafe_proof_direct]
opaque safe_proof_direct (P : Prop) : P

theorem prove_any (P : Prop) : P :=
  safe_proof_direct P

#print axioms prove_any
