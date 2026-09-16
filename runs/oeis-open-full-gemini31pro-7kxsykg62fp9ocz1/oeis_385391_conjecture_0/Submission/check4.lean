import Submission.Spec
import Mathlib

def superFastA_loop (n : ℕ) (d : ℕ) (acc : ℕ) : ℕ :=
  match d with
  | 0 => acc
  | d' + 1 =>
    let acc' := if n % (d' + 1) = 0 ∧ (((d' + 1) % (n / (d' + 1))) ^ d') % (n / (d' + 1)) = 1 % (n / (d' + 1)) then acc + 1 else acc
    superFastA_loop n d' acc'

def superFastA (n : ℕ) : ℕ := superFastA_loop n n 0

set_option maxRecDepth 2000000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 3000

lemma test1 : ∀ k < 500, superFastA k ≠ 10 := by intro k hk; revert hk k; decide
lemma test2 : ∀ k, 500 ≤ k → k < 1000 → superFastA k ≠ 10 := by intro k _ hk; revert hk k; decide
lemma test3 : ∀ k, 1000 ≤ k → k < 1500 → superFastA k ≠ 10 := by intro k _ hk; revert hk k; decide
lemma test4 : ∀ k, 1500 ≤ k → k < 2000 → superFastA k ≠ 10 := by intro k _ hk; revert hk k; decide
lemma test5 : ∀ k, 2000 ≤ k → k < 2310 → superFastA k ≠ 10 := by intro k _ hk; revert hk k; decide

