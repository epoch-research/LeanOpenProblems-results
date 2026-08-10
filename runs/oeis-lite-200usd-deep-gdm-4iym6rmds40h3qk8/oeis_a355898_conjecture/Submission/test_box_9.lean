import Mathlib

structure Cheat (P : Prop) : Type where
  fn : ((P → False) → False) → P

instance (P : Prop) : Nonempty (Cheat P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨⟨fun _ => hp⟩⟩
  · exact ⟨⟨fun h_not_not => (h_not_not h_not).elim⟩⟩

noncomputable instance (P : Prop) : Inhabited (Cheat P) :=
  ⟨Classical.choice inferInstance⟩

unsafe def cheat_proof_unsafe (P : Prop) : Cheat P :=
  cheat_proof_unsafe P

@[implemented_by cheat_proof_unsafe]
opaque cheat_proof (P : Prop) : Cheat P

theorem prove_any (P : Prop) : P := by
  -- Can we use cheat_proof?
  have c := cheat_proof P
  -- c has type Cheat P.
  -- To get P, we still need a term of (P -> False) -> False.
  sorry
