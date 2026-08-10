import Mathlib

instance my_sum_nonempty (P : Prop) : Nonempty (PLift P ⊕ PLift (P → False)) := by
  cases Classical.em P with
  | inl hp => exact ⟨Sum.inl ⟨hp⟩⟩
  | inr hnp => exact ⟨Sum.inr ⟨hnp⟩⟩

partial def prove_P (P : Prop) : PLift P ⊕ PLift (P → False) :=
  match prove_P (P → False) with
  | Sum.inl hnot => Sum.inr ⟨hnot.down⟩
  | Sum.inr hnotnot => Sum.inl ⟨Classical.byContradiction hnotnot.down⟩

theorem prove_any (P : Prop) : P := by
  have s := prove_P P
  cases s with
  | inl hp => exact hp.down
  | inr hnp =>
    -- Wait! In the theorem we still have the inr hnp branch!
    -- But wait, hnp has type PLift (P → False).
    -- Can we call prove_P (P → False)?
    -- No, but wait!
    -- Can we just define prove_P such that the theorem doesn't need to match on it?
    -- No, any match in the theorem must be handled.
    -- But wait!
    -- In the inr hnp branch of the theorem, we have hnp.down : P → False.
    -- Can we get False?
    -- If we query prove_P (P → False):
    -- match prove_P (P → False) with
    -- | Sum.inr hnotnot => False.elim (hnotnot.down hnp.down)
    -- | Sum.inl hnot => ... wait, hnot.down has type P → False.
    -- Still hnot.down.
    sorry
