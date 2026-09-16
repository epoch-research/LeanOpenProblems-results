import Submission.Spec
import Mathlib
open Nat Finset

lemma a_ge_three_primes_ne {n p q : ℕ} (hn_pos : 0 < n) (hdp : p ∣ n) (hdq : q ∣ n) (h1 : p ≠ q) :
  n / p ≠ n / q := by
  intro h
  have h_eq1 : (n / p) * p = (n / q) * p := by rw [h]
  rw [Nat.div_mul_cancel hdp] at h_eq1
  have h_eq2 : n * q = (n / q) * p * q := by rw [← h_eq1]
  have h_assoc : (n / q) * p * q = (n / q) * q * p := by ring
  rw [h_assoc, Nat.div_mul_cancel hdq] at h_eq2
  have h_pq : q = p := mul_left_cancel₀ hn_pos.ne.symm h_eq2
  exact h1 h_pq.symm
