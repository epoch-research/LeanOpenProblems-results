import Submission.Spec
import Mathlib

set_option maxHeartbeats 0

def fast_a_loop (n : ℕ) : ℕ → ℕ → ℕ
| 0, acc => acc
| s' + 1, acc => fast_a_loop n s' (acc + if Nat.Prime (n^2 + (s'+1)^2) then 1 else 0)

def fast_a (n : ℕ) : ℕ := fast_a_loop n (n-1) 0

lemma fast_a_loop_eq (n : ℕ) (s : ℕ) (acc : ℕ) :
  fast_a_loop n s acc = acc + (Finset.Ico 1 (s + 1)).sum (fun x => if Nat.Prime (n^2 + x^2) then 1 else 0) := by
  induction s generalizing acc with
  | zero =>
    simp [fast_a_loop]
  | succ s' ih =>
    rw [fast_a_loop, ih]
    have h1 : 1 ≤ s' + 1 := by omega
    rw [Finset.sum_Ico_succ_top h1]
    omega

lemma fast_a_eq_a (n : ℕ) (h : 1 < n) : fast_a n = a n := by
  unfold fast_a a
  have h_eq := fast_a_loop_eq n (n - 1) 0
  have h_s : n - 1 + 1 = n := by omega
  rw [h_s] at h_eq
  rw [zero_add] at h_eq
  exact h_eq
