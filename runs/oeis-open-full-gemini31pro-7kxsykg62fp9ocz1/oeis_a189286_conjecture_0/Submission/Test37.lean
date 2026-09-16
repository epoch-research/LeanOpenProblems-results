import Submission.Spec
open Nat Finset

lemma div_test (n : ℕ) : 
  (2*n - 1) * (3*n).choose n ∣ Finset.sum (range (n + 1)) fun k => T_term k * T_term (n - k) := by
  sorry
