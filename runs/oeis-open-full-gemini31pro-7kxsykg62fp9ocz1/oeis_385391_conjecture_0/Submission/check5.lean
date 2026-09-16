import Submission.Spec
import Mathlib

def fastA384237 (n : ℕ) : ℕ :=
  (n.divisors.filter fun d => ((d % (n / d)) ^ (d - 1)) % (n / d) = 1 % (n / d)).card

set_option maxRecDepth 2000000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 3000

lemma test1 : ∀ k < 500, fastA384237 k ≠ 10 := by intro k hk; revert hk k; decide
lemma test2 : ∀ k, 500 ≤ k → k < 1000 → fastA384237 k ≠ 10 := by intro k _ hk; revert hk k; decide
lemma test3 : ∀ k, 1000 ≤ k → k < 1500 → fastA384237 k ≠ 10 := by intro k _ hk; revert hk k; decide
lemma test4 : ∀ k, 1500 ≤ k → k < 2000 → fastA384237 k ≠ 10 := by intro k _ hk; revert hk k; decide
lemma test5 : ∀ k, 2000 ≤ k → k < 2310 → fastA384237 k ≠ 10 := by intro k _ hk; revert hk k; decide
