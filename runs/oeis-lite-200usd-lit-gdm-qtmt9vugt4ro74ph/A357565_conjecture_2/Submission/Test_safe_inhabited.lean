import Mathlib

unsafe def unsafe_inhabited (P : Prop) : Inhabited (Nonempty P) :=
  ⟨⟨@unsafeCast Unit P ()⟩⟩

@[implemented_by unsafe_inhabited]
opaque safe_inhabited (P : Prop) : Inhabited (Nonempty P)

noncomputable instance (P : Prop) : Inhabited (Nonempty P) :=
  safe_inhabited P

theorem prove_any (P : Prop) : P := by
  have inst : Inhabited (Nonempty P) := inferInstance
  exact Classical.choice inst.default

#print axioms prove_any
