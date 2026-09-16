import Mathlib
import Submission.Spec

open Nat BigOperators

lemma a_def_eq (n : ℕ) (hn : n > 2) :
  a (n - 1) * (n - 1).factorial = 2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := by
  have h_n_1_ne_0 : n - 1 ≠ 0 := by omega
  unfold a
  rw [dif_neg h_n_1_ne_0]
  -- now it's (numerator / denominator) * denominator
  -- we must prove denominator | numerator to use Nat.div_mul_cancel
  sorry
