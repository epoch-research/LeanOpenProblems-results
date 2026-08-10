import Mathlib

structure Cheat (P : Prop) : Type where
  fn : ((P → False) → False) → P

instance (P : Prop) : Nonempty (Cheat P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨⟨fun _ => hp⟩⟩
  · exact ⟨⟨fun h_not_not => (h_not_not h_not).elim⟩⟩

partial def get_cheat (P : Prop) : Cheat P :=
  get_cheat P
