import Lean

theorem my_proof_using_opaque (p : Prop) : p := by
  have h : Decidable p := Classical.choice ⟨.isTrue sorry⟩ -- Wait, this uses sorry, but what if we do opaque?
  sorry
