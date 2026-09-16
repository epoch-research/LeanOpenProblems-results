import Submission.Spec
open Nat Finset

lemma div_test_each (n k : ℕ) (h : k ≤ n) : 
  (2*n - 1) * (3*n).choose n ∣ T_term k * T_term (n - k) := by
  sorry
