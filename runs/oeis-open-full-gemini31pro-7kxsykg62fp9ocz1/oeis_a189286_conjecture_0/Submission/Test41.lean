import Submission.Spec
open Nat Finset

lemma T_term_expand (k : ℕ) : T_term k = (6*k).factorial / ((3*k).factorial * (2*k).factorial * k.factorial) := by
  sorry

lemma D_expand (n : ℕ) : (2*n - 1) * (3*n).choose n = (3*n).factorial / (n.factorial * (2*n - 1).factorial * 2 * n) := by
  sorry
