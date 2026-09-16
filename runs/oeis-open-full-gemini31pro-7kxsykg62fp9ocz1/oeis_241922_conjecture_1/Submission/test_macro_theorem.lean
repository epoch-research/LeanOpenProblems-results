import Submission.Spec
open Nat

macro_rules | `(goldbach_binary_conjecture) => `(True)

theorem oeis_241922_conjecture_1_macro :
  goldbach_binary_conjecture ↔ ¬ ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n := by
  sorry
