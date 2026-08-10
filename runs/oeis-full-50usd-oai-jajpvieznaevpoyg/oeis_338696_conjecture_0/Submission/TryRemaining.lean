import Submission.Spec

open Nat BigOperators Finset

example (n : ℕ) (hn : n ≠ 19) : A338696 n > 0 := by
  aesop (add safe A338696_pos_of_witness)

example (n : ℕ) (hn : n ≠ 19) : A338696 n > 0 := by
  grind [A338696, A338696_pos_of_witness]
