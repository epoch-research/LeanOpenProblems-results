import Submission.Spec

open Nat

lemma test_induction_step_congruence (k : ℕ)
    (h_ih : num (k + 2) % (2 * den (k + 2)) = (choose (k + 1) ((k + 2) / 2) * den (k + 2)) % (2 * den (k + 2))) :
    num (k + 3) % (2 * den (k + 3)) = (choose (k + 2) ((k + 3) / 2) * den (k + 3)) % (2 * den (k + 3)) := by
  sorry
