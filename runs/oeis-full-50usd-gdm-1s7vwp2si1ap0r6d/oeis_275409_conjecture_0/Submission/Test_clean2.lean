def Pall : Prop := False

unsafe def unsafe_proof (inst : Inhabited (Nonempty Pall)) : Nonempty Pall :=
  unsafe_proof inst

@[implemented_by unsafe_proof]
opaque safe_proof (inst : Inhabited (Nonempty Pall)) : Nonempty Pall

unsafe instance : Inhabited (Nonempty Pall) where
  default := unsafe_proof (by infer_instance)

-- Wait, can we now define a safe theorem?
theorem safe_theorem : Pall := by
  have inst : Inhabited (Nonempty Pall) := by infer_instance
  have h := safe_proof inst
  cases h
  assumption
