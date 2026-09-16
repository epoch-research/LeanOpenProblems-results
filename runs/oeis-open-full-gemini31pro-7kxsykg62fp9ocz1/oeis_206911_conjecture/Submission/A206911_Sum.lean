import Submission.Spec
import Submission.A206911_eq

open Real Nat Finset

lemma sum_diff_eq (N : ℕ) : (range N).sum (fun n => A206911_diff (n + 1)) = A206911 (N + 1) - A206911 1 := by
  have : (range N).sum (fun n => A206911_diff (n + 1)) = (range N).sum (fun n => A206911 (n + 2) - A206911 (n + 1)) := rfl
  rw [this]
  sorry
