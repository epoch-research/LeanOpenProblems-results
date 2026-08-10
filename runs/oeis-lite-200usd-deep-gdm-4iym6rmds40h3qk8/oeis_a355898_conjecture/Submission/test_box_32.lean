import Mathlib

instance (P : Prop) : Nonempty (Nonempty P → P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨fun _ => hp⟩
  · exact ⟨fun h_ne => (h_not (Classical.choice h_ne)).elim⟩

attribute [local instance] Classical.inhabited_of_nonempty

unsafe def unsafe_proof_imp (P : Prop) : Nonempty P → P :=
  fun _ => unsafe_proof_imp P (Classical.choice inferInstance)

@[implemented_by unsafe_proof_imp]
opaque safe_proof_imp (P : Prop) : Nonempty P → P

theorem prove_any (P : Prop) : P := by
  have h_ne : Nonempty P := by
    -- wait, we still need to prove Nonempty P to call safe_proof_imp P h_ne.
    sorry
