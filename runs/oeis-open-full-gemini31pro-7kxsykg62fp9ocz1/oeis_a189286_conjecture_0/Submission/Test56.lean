import Submission.Spec
open Nat Finset

lemma a189286_sum_div (n : ℕ) :
  (2*n - 1) * (3*n).choose n ∣ ∑ k ∈ range (n + 1), T_term k * T_term (n - k) := by
  sorry
