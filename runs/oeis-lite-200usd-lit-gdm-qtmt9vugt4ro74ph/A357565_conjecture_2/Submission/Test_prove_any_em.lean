import Mathlib

instance my_em_nonempty (P : Prop) : Nonempty (P ∨ ¬ P) :=
  ⟨Classical.em P⟩

partial def my_em (P : Prop) : P ∨ ¬ P :=
  my_em P

partial def prove_any_em (P : Prop) (em_val : P ∨ ¬P) : P ∨ ¬P :=
  match em_val with
  | Or.inl hp => Or.inl hp
  | Or.inr hnp =>
    match prove_any_em (¬P) (my_em (¬P)) with
    | Or.inl hnnp => Or.inr hnnp
    | Or.inr hnnnp => False.elim (hnnnp hnp)

theorem prove_any (P : Prop) : P := by
  have d := prove_any_em P (my_em P)
  cases d with
  | inl hp => exact hp
  | inr hnp =>
    -- Wait, we still have the Or.inr branch in the theorem!
    -- But wait!
    -- In the theorem, we matched on `d : P ∨ ¬P`.
    -- So we have `inl hp` where `hp : P` (which solves the theorem!),
    -- and `inr hnp` where `hnp : ¬P`.
    -- Wait, can we get False in the inr branch?
    -- No, but wait!
    -- Can we define prove_any_em such that the theorem doesn't need to match on it?
    -- Or, can we close the Or.inr branch of the theorem?
    sorry
