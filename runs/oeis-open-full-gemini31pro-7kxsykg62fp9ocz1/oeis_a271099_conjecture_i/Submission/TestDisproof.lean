import Submission.Spec
open Nat Finset

theorem disproof : ¬ ((∀ n : ℕ, A271099 n > 0) ∧ (∀ n : ℕ, A271099 n = 1 ↔ n ∈ A271099_lone_count_set)) := by decide
