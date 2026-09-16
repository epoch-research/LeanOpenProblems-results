import Submission.Spec
open Nat Finset

#check ∃ x y : ℕ, ∃ z : ℤ,
  (P_k_first 5 x) + (P_k_second 5 y) + (polygonal_num_val 10 z).toNat = 0
