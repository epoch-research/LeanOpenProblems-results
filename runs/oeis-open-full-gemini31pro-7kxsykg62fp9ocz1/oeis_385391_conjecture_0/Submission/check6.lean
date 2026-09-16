import Submission.Spec
import Mathlib

lemma A384237_cond_eq (n d : ℕ) (hd : d ∣ n) (hd0 : d > 0) :
    (d ^ d) % n = d % n ↔ ((d % (n / d)) ^ (d - 1)) % (n / d) = 1 % (n / d) := by
  generalize h_m : n / d = m
  have hn : n = m * d := by rw [← h_m, Nat.div_mul_cancel hd]
  have hd_pow : d ^ d = d ^ (d - 1) * d := by
    calc d ^ d = d ^ (d - 1 + 1) := by rw [Nat.sub_add_cancel hd0]
      _ = d ^ (d - 1) * d := by rw [pow_succ]
  subst hn
  rw [hd_pow]
  have h1 : d % (m * d) = (1 % m) * d := by
    calc d % (m * d) = (1 * d) % (m * d) := by rw [Nat.one_mul]
      _ = (1 % m) * d := Nat.mul_mod_mul_right d 1 m
  rw [Nat.mul_mod_mul_right, h1]
  rw [← Nat.pow_mod]
  constructor
  · intro h
    exact Nat.eq_of_mul_eq_mul_right hd0 h
  · intro h
    rw [h]

def fastA384237 (n : ℕ) : ℕ :=
  (n.divisors.filter fun d => ((d % (n / d)) ^ (d - 1)) % (n / d) = 1 % (n / d)).card

set_option maxRecDepth 2000000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 3000

lemma test1 : ∀ k, 1 ≤ k → k < 300 → fastA384237 k ≠ 10 := by intro k _ hk; revert hk k; decide
lemma test2 : ∀ k, 300 ≤ k → k < 600 → fastA384237 k ≠ 10 := by intro k _ hk; revert hk k; decide
lemma test3 : ∀ k, 600 ≤ k → k < 900 → fastA384237 k ≠ 10 := by intro k _ hk; revert hk k; decide
lemma test4 : ∀ k, 900 ≤ k → k < 1200 → fastA384237 k ≠ 10 := by intro k _ hk; revert hk k; decide
lemma test5 : ∀ k, 1200 ≤ k → k < 1500 → fastA384237 k ≠ 10 := by intro k _ hk; revert hk k; decide
lemma test6 : ∀ k, 1500 ≤ k → k < 1800 → fastA384237 k ≠ 10 := by intro k _ hk; revert hk k; decide
lemma test7 : ∀ k, 1800 ≤ k → k < 2100 → fastA384237 k ≠ 10 := by intro k _ hk; revert hk k; decide
lemma test8 : ∀ k, 2100 ≤ k → k < 2310 → fastA384237 k ≠ 10 := by intro k _ hk; revert hk k; decide

