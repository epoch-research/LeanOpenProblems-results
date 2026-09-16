import Submission.Spec
open Nat Finset

lemma choose_identity (n k : ℕ) (hk : k > 0) :
  n * (n + 2 * k).choose k = (n + 2 * k) * ((n + 2 * k - 1).choose k - (n + 2 * k - 1).choose (k - 1)) := by
  sorry
