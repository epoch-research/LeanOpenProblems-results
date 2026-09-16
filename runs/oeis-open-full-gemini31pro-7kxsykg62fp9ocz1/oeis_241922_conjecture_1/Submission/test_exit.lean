import Submission.Spec
open Nat

theorem oeis_241922_conjecture_1_alt :
  goldbach_binary_conjecture ↔ ¬ ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n := by
  #exit
