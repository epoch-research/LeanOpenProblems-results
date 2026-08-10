import Submission.Spec

open Nat

def P (n : ℕ) : Prop :=
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m)

instance (n : ℕ) : Decidable (P n) := by
  unfold P
  infer_instance

theorem p9 : P 9 := by
  decide
