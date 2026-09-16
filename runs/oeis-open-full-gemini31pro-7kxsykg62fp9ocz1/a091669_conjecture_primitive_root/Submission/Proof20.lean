import Mathlib
import Submission.Spec
import Submission.Proof18

open Nat BigOperators

lemma a_mul_fact (n : ℕ) (hn : n > 2) :
  a (n - 1) * (n - 1).factorial = 2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := by
  have hn1 : n - 1 ≠ 0 := by omega
  unfold a
  rw [dif_neg hn1]
  have h_div : (n - 1).factorial ∣ 2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := exact_div n hn
  exact Nat.div_mul_cancel h_div
