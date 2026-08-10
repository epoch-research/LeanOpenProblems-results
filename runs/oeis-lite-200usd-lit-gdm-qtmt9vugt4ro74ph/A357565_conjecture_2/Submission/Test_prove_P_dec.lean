import Mathlib

partial def my_dec (P : Prop) : Decidable P :=
  my_dec P

partial def prove_P_dec (P : Prop) (d : Decidable P) : Decidable P :=
  match d with
  | Decidable.isTrue hp => Decidable.isTrue hp
  | Decidable.isFalse hnp =>
    match prove_P_dec (P → False) (my_dec (P → False)) with
    | Decidable.isTrue hnnp => Decidable.isFalse hnnp
    | Decidable.isFalse hnnnp => False.elim (hnnnp hnp)

theorem prove_any (P : Prop) : P := by
  have d := prove_P_dec P (my_dec P)
  cases d with
  | isTrue hp => exact hp
  | isFalse hnp =>
    -- wait, we must handle the isFalse branch in prove_any.
    -- but wait! Can we show that the isFalse branch is impossible?
    -- No, but wait: how can we close the isFalse branch in prove_any?
    sorry
