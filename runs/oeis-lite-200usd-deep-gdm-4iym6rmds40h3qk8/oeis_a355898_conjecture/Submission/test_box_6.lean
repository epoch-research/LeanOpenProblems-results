import Mathlib

structure Cheat (P : Prop) : Type where
  fn : ((P → False) → False) → P

instance (P : Prop) : Nonempty (Cheat P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨⟨fun _ => hp⟩⟩
  · exact ⟨⟨fun h_not_not => (h_not_not h_not).elim⟩⟩

partial def get_cheat (P : Prop) : Cheat P :=
  get_cheat P

-- Can we prove False?
theorem prove_false : False := by
  -- We want to construct a term of type (False -> False) -> False
  have h_not_not : (False → False) → False := by
    intro h
    exact h (id) -- wait, h has type False -> False. So h (id) is not correct.
    -- If h : False -> False, how to get False?
    -- We can't, unless we have a term of False.
    sorry
