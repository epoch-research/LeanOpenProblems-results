import Submission.Spec
open Nat

set_option pp.all true

#check (Even 2)
#check (Nat.Prime 2)

lemma p : (∀ n : ℕ, Even n ∧ n > 2 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q) := by
  sorry
