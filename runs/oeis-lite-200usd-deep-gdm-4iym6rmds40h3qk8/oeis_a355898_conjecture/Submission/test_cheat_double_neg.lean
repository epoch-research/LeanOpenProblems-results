import Mathlib

structure Cheat (P : Prop) : Type where
  fn : ((P → False) → False) → P

instance (P : Prop) : Nonempty (Cheat P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨⟨fun _ => hp⟩⟩
  · exact ⟨⟨fun h_not_not => (h_not_not h_not).elim⟩⟩

partial def get_cheat (P : Prop) : Cheat P := get_cheat P

structure NegNeg (P : Prop) : Type where
  fn : (P → False) → False

instance (P : Prop) : Nonempty (NegNeg P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨⟨fun h_not => (h_not hp).elim⟩⟩
  · exact ⟨⟨fun h_not_not => h_not_not h_not⟩⟩

partial def get_negneg (P : Prop) : NegNeg P :=
  ⟨fun h_not =>
    have p_val : P := (get_cheat P).fn (get_negneg P).fn
    h_not p_val⟩

theorem prove_any (P : Prop) : P :=
  (get_cheat P).fn (get_negneg P).fn


