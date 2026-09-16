import Submission.Spec
open Nat

set_option pp.all true

#check (Even 2)
#check (Nat.Prime 2)

lemma lemma_disproof : ¬ (goldbach_binary_conjecture ↔ ¬ ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n) := by
  sorry
