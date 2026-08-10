import Mathlib

theorem test_choice (P : Prop) : P := by
  have h : Nonempty (P ⊕ (P → False)) := by
    by_cases hP : P
    · exact ⟨Sum.inl hP⟩
    · exact ⟨Sum.inr hP⟩
  have val := Classical.choice h
  cases val with
  | inl hp => exact hp
  | inr hnf =>
    -- We have hnf : P → False.
    -- Can we get P? No, because we only have P → False, we don't have P.
    sorry
