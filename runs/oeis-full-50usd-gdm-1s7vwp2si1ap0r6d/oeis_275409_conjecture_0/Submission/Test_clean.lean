def Pall : Prop := True

@[implemented_by unsafe_proof]
opaque safe_proof : Pall

unsafe def unsafe_proof : Pall :=
  unsafe_proof
