import Mathlib
import Submission.ProofCases21
import Submission.ProofBound
import Submission.ProofFinal

open Nat Finset

lemma a_bound_pk2 {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
  (p ^ k).divisors.sum (fun d => (d : ℚ) * (Nat.divisors d).card) <
  (p ^ k : ℚ) * ((k + 1 : ℕ) : ℚ) * ((p : ℚ) / ((p : ℚ) - 1)) := by
  rw [a_bound_pk hp]
  have h_bound := S_prime_pow_lt hp.two_le (k := k)
  have hpk_pos : 0 < (p ^ k : ℚ) := by
    have : 0 < p := hp.pos
    have : 0 < p ^ k := Nat.pos_of_ne_zero (pow_ne_zero k hp.ne_zero)
    exact_mod_cast this
  have := mul_lt_mul_of_pos_left h_bound hpk_pos
  have h_assoc : (p ^ k : ℚ) * (((k + 1 : ℕ) : ℚ) * ((p : ℚ) / ((p : ℚ) - 1))) = (p ^ k : ℚ) * ((k + 1 : ℕ) : ℚ) * ((p : ℚ) / ((p : ℚ) - 1)) := by ring
  rwa [← h_assoc]
