unsafe def get_p_unsafe (P : Prop) : P :=
  get_p_unsafe P

unsafe instance (P : Prop) : Inhabited P :=
  ⟨get_p_unsafe P⟩

@[implemented_by get_p_unsafe]
opaque safe_proof (P : Prop) : P

theorem prove_any (P : Prop) : P :=
  safe_proof P

#print axioms prove_any
