import Submission.Spec

example (n : ℕ) (hn : n ≠ 19) (hsmall : ¬ n < 2000) : A338696 n > 0 := by
  have hn2 : 2000 ≤ n := by omega
  -- try a few automation tactics
  aesop (add safe A338696_pos_of_nat_z_witness A338696_pos_of_neg_z_witness A338696_pos_of_int_z_witness)
