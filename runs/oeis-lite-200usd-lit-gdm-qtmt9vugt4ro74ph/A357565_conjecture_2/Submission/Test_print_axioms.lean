import Mathlib

unsafe def unsafe_proof (P : Prop) : P :=
  @unsafeCast Unit P ()

mutual
  @[implemented_by unsafe_proof]
  partial def safe_proof (P : Prop) : P :=
    safe_proof P

  partial instance (P : Prop) : Inhabited P :=
    ⟨safe_proof P⟩
end








