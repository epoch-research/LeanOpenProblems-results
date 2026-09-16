import Submission.Spec
import Mathlib
import Submission.ProofFinal

open Nat Finset

lemma a_ge_three_primes_step {n p : ℕ} (hn_pos : 0 < n) (hp : p.Prime) (hdp : p ∣ n) :
  n / p ∈ n.divisors.erase n := by
  rw [mem_erase, mem_divisors]
  refine ⟨?_, ⟨Nat.div_dvd_of_dvd hdp, hn_pos.ne.symm⟩⟩
  intro h
  have hn_eq : n / p * p = n := Nat.div_mul_cancel hdp
  rw [h] at hn_eq
  have : n * 1 = n * p := by
    calc n * 1 = n := by ring
      _ = n * p := hn_eq.symm
  have hp1 : 1 = p := mul_left_cancel₀ hn_pos.ne.symm this
  have : 2 ≤ p := hp.two_le
  omega

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

lemma a_ge_three_primes {n p q r : ℕ} (hn_pos : 0 < n) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
  (h1 : p ≠ q) (h2 : q ≠ r) (h3 : p ≠ r)
  (hdp : p ∣ n) (hdq : q ∣ n) (hdr : r ∣ n) :
  4 * (n / p) + 4 * (n / q) + 4 * (n / r) ≤ a n := by
  have hd_p : n / p ∈ n.divisors.erase n := a_ge_three_primes_step hn_pos hp hdp
  have hd_q : n / q ∈ n.divisors.erase n := a_ge_three_primes_step hn_pos hq hdq
  have hd_r : n / r ∈ n.divisors.erase n := a_ge_three_primes_step hn_pos hr hdr
  have h_sub : {n / p, n / q, n / r} ⊆ n.divisors.erase n := by
    intro d hd
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact hd_p
    · exact hd_q
    · exact hd_r
  have hpq_ne : n / p ≠ n / q := a_ge_three_primes_ne hn_pos hdp hdq h1
  have hqr_ne : n / q ≠ n / r := a_ge_three_primes_ne hn_pos hdq hdr h2
  have hpr_ne : n / p ≠ n / r := a_ge_three_primes_ne hn_pos hdp hdr h3
  have h_card : ({n / p, n / q, n / r} : Finset ℕ).card = 3 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
    · simp only [mem_singleton]
      exact hqr_ne
    · simp only [mem_insert, mem_singleton]
      push_neg
      exact ⟨hpq_ne, hpr_ne⟩
  rw [a_eq_sum_proper hn_pos]
  have h_sum : ({n / p, n / q, n / r} : Finset ℕ).sum (fun d => d * (Nat.divisors d).card) ≤ ∑ d ∈ n.divisors.erase n, d * (Nat.divisors d).card := by
    exact sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => Nat.zero_le _)
  have h_eval : ({n / p, n / q, n / r} : Finset ℕ).sum (fun d => d * (Nat.divisors d).card) = 
    (n / p) * (Nat.divisors (n / p)).card + (n / q) * (Nat.divisors (n / q)).card + (n / r) * (Nat.divisors (n / r)).card := by
    rw [sum_insert, sum_insert, sum_singleton]
    · simp only [mem_singleton]
      exact hqr_ne
    · simp only [mem_insert, mem_singleton]
      push_neg
      exact ⟨hpq_ne, hpr_ne⟩
  rw [h_eval] at h_sum
  have h_tau_p : 4 ≤ (Nat.divisors (n / p)).card := tau_div_ge_four hn_pos hp hq hr h1 h2 h3 hdp hdq hdr
  have h_tau_q : 4 ≤ (Nat.divisors (n / q)).card := tau_div_ge_four hn_pos hq hp hr h1.symm h3.symm h2 hdq hdp hdr
  have h_tau_r : 4 ≤ (Nat.divisors (n / r)).card := tau_div_ge_four hn_pos hr hp hq h3.symm h1 h2.symm hdr hdp hdq
  calc 4 * (n / p) + 4 * (n / q) + 4 * (n / r) ≤ (n / p) * 4 + (n / q) * 4 + (n / r) * 4 := by ring_nf; rfl
    _ ≤ (n / p) * (Nat.divisors (n / p)).card + (n / q) * (Nat.divisors (n / q)).card + (n / r) * (Nat.divisors (n / r)).card := by
      gcongr
    _ ≤ ∑ d ∈ n.divisors.erase n, d * (Nat.divisors d).card := h_sum

