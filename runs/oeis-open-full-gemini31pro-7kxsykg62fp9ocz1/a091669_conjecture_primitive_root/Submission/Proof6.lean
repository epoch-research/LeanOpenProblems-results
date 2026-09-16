import Mathlib
import Submission.Spec
import Submission.Proof5

open Nat BigOperators

lemma digits_sum_pos (p n : ℕ) (hp : p > 1) (hn : n > 0) :
  (p.digits n).sum ≥ 1 := by
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.digits_def' hp hn]
  simp only [List.sum_cons]
  by_cases h0 : n / p = 0
  · have h_mod : n % p = n := by
      have : n < p := by
        by_contra h
        have : 0 < n / p := Nat.div_pos (by omega) (by omega)
        omega
      exact Nat.mod_eq_of_lt this
    omega
  · have h_div_pos : n / p > 0 := Nat.pos_of_ne_zero h0
    have h_lt : n / p < n := Nat.div_lt_self hn hp
    have := ih (n / p) h_lt h_div_pos
    omega

lemma digits_sum_ge_p (n p : ℕ) [hp : Fact p.Prime] (hn2 : n > 2) (hcomp : ¬ n.Prime) (hdvd : p ∣ n) :
  (p.digits (n - 1)).sum ≥ p := by
  have hk : ∃ k, n = p * k := exists_eq_mul_right_of_dvd hdvd
  rcases hk with ⟨k, rfl⟩
  have hk2 : k ≥ 2 := by
    by_contra h
    have h1 : k < 2 := by omega
    rcases k with _ | _ | _
    · omega
    · have : p * 1 = p := mul_one p
      rw [this] at hcomp
      exact hcomp hp.out
    · omega
  have h_p2 : p ≥ 2 := hp.out.two_le
  have mod_div := mod_div_trick p k h_p2 hk2
  have h_n1_pos : p * k - 1 > 0 := by
    have : p * k ≥ 4 := by nlinarith
    omega
  rw [Nat.digits_def' (by omega) h_n1_pos]
  simp only [List.sum_cons]
  rw [mod_div.1, mod_div.2]
  have h_k_1_pos : k - 1 > 0 := by omega
  have := digits_sum_pos p (k - 1) (by omega) h_k_1_pos
  omega
