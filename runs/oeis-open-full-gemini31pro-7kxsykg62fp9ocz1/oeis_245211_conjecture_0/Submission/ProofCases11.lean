import Submission.Spec
import Mathlib

open Nat Finset

lemma dvd_div_of_distinct_primes {n p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hdp : p ∣ n) (hdq : q ∣ n) :
  q ∣ n / p := by
  have h_coprime : p.Coprime q := by
    rw [hp.coprime_iff_not_dvd]
    intro h
    exact hpq.symm ((hq.eq_one_or_self_of_dvd p h).resolve_left hp.ne_one).symm
  have h_dvd_mul : p * q ∣ n := h_coprime.mul_dvd_of_dvd_of_dvd hdp hdq
  have ⟨k, hk⟩ := h_dvd_mul
  use k
  have : n / p = q * k := by
    rw [hk]
    have h_assoc : p * q * k = p * (q * k) := by ring
    rw [h_assoc]
    exact Nat.mul_div_cancel_left _ hp.pos
  rw [this]

lemma tau_ge_four {m q r : ℕ} (hm : 0 < m) (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r) (hdq : q ∣ m) (hdr : r ∣ m) :
  4 ≤ (Nat.divisors m).card := by
  have h_coprime : q.Coprime r := by
    rw [hq.coprime_iff_not_dvd]
    intro h
    exact hqr.symm ((hr.eq_one_or_self_of_dvd q h).resolve_left hq.ne_one).symm
  have hdvd : q * r ∣ m := h_coprime.mul_dvd_of_dvd_of_dvd hdq hdr
  have h_sub : {q * r, r, q, 1} ⊆ m.divisors := by
    intro d hd
    rw [mem_divisors]
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨hdvd, hm.ne.symm⟩
    · exact ⟨hdr, hm.ne.symm⟩
    · exact ⟨hdq, hm.ne.symm⟩
    · exact ⟨one_dvd m, hm.ne.symm⟩
  have h_card : ({q * r, r, q, 1} : Finset ℕ).card = 4 := by
    have hq2 : 2 ≤ q := hq.two_le
    have hr2 : 2 ≤ r := hr.two_le
    have h1 : q * r ∉ ({r, q, 1} : Finset ℕ) := by
      simp only [mem_insert, mem_singleton]
      push_neg
      constructor
      · intro h; nlinarith
      · constructor
        · intro h; nlinarith
        · intro h; nlinarith
    have h2 : r ∉ ({q, 1} : Finset ℕ) := by
      simp only [mem_insert, mem_singleton]
      push_neg
      exact ⟨hqr.symm, hr.ne_one⟩
    have h3 : q ∉ ({1} : Finset ℕ) := by
      simp only [mem_singleton]
      exact hq.ne_one
    rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_insert_of_notMem h3, card_singleton]
  rw [← h_card]
  exact card_le_card h_sub

lemma tau_div_ge_four {n p q r : ℕ} (hn_pos : 0 < n) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) 
  (h1 : p ≠ q) (h2 : q ≠ r) (h3 : p ≠ r)
  (hdp : p ∣ n) (hdq : q ∣ n) (hdr : r ∣ n) :
  4 ≤ (Nat.divisors (n / p)).card := by
  have h_pos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn_pos hdp) hp.pos
  have hdq_div : q ∣ n / p := dvd_div_of_distinct_primes hp hq h1 hdp hdq
  have hdr_div : r ∣ n / p := dvd_div_of_distinct_primes hp hr h3 hdp hdr
  exact tau_ge_four h_pos hq hr h2 hdq_div hdr_div
