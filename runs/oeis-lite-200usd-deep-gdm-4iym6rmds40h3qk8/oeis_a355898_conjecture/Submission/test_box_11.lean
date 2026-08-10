import Mathlib

instance (P : Prop) : Nonempty (Nonempty P → P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨fun _ => hp⟩
  · exact ⟨fun h_ne => (h_not (Classical.choice h_ne)).elim⟩

partial def get_imp (P : Prop) : Nonempty P → P :=
  get_imp P
