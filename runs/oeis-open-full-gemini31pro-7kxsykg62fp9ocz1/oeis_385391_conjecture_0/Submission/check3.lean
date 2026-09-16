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

lemma A384237_eq_fastA384237 (n : ℕ) : A384237 n = fastA384237 n := by
  dsimp [A384237, fastA384237]
  congr 1
  apply Finset.filter_congr
  intro d hd
  have hd_div : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hd_pos : d > 0 := by
    have hn0 : n ≠ 0 := (Nat.mem_divisors.mp hd).2
    exact Nat.pos_of_ne_zero (fun h => by subst h; exact hn0 (eq_zero_of_zero_dvd hd_div))
  exact A384237_cond_eq n d hd_div hd_pos


set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 3000

lemma test : ∀ k < 2310, fastA384237 k ≠ 10 := by
  intro k hk; revert hk k; decide
