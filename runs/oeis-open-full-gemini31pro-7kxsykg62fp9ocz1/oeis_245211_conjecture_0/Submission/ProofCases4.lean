import Submission.Spec
import Mathlib
import Submission.ProofCases3

open Nat Finset


lemma a_pq (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) : a (p * q) = 1 + 2 * p + 2 * q := by
  have h_divs := divisors_pq hp hq hpq
  have h_ne1 : p * q ≠ q := by
    intro h
    have : p * q = 1 * q := by rw [h, one_mul]
    have hp1 : p = 1 := mul_right_cancel₀ hq.pos.ne.symm this
    have := hp.two_le; omega
  have h_ne2 : p * q ≠ p := by
    intro h
    have : p * q = p * 1 := by rw [h, mul_one]
    have hq1 : q = 1 := mul_left_cancel₀ hp.pos.ne.symm this
    have := hq.two_le; omega
  have h_ne3 : p * q ≠ 1 := by
    have := hp.two_le; have := hq.two_le; nlinarith
  have h_ne4 : q ≠ p := hpq.symm
  have h_ne5 : q ≠ 1 := by have := hq.two_le; omega
  have h_ne6 : p ≠ 1 := by have := hp.two_le; omega
  
  have h_not_mem1 : p ∉ ({1} : Finset ℕ) := by rw [mem_singleton]; exact h_ne6
  have h_not_mem2 : q ∉ ({p, 1} : Finset ℕ) := by
    rw [mem_insert, mem_singleton]
    push_neg
    exact ⟨h_ne4, h_ne5⟩
  have h_not_mem3 : p * q ∉ ({q, p, 1} : Finset ℕ) := by
    rw [mem_insert, mem_insert, mem_singleton]
    push_neg
    exact ⟨h_ne1, h_ne2, h_ne3⟩
    
  have h_tau_p : (Nat.divisors p).card = 2 := by
    have hd : p.divisors = {p, 1} := by
      ext x
      rw [hp.divisors, mem_insert, mem_insert, mem_singleton, mem_singleton]
      tauto
    rw [hd, card_insert_of_notMem h_not_mem1, card_singleton]
  have h_tau_q : (Nat.divisors q).card = 2 := by
    have hq_not : q ∉ ({1} : Finset ℕ) := by rw [mem_singleton]; exact h_ne5
    have hd : q.divisors = {q, 1} := by
      ext x
      rw [hq.divisors, mem_insert, mem_insert, mem_singleton, mem_singleton]
      tauto
    rw [hd, card_insert_of_notMem hq_not, card_singleton]
  have h_tau_pq : (Nat.divisors (p * q)).card = 4 := by
    rw [h_divs, card_insert_of_notMem h_not_mem3, card_insert_of_notMem h_not_mem2, card_insert_of_notMem h_not_mem1, card_singleton]
  have h_tau_1 : (Nat.divisors 1).card = 1 := rfl
  
  unfold a
  change (p * q).divisors.sum (fun d => d * (Nat.divisors d).card) - (p * q) * (p * q).divisors.card = 1 + 2 * p + 2 * q
  rw [h_divs]
  
  have h_card : ({p * q, q, p, 1} : Finset ℕ).card = 4 := by
    rw [card_insert_of_notMem h_not_mem3, card_insert_of_notMem h_not_mem2, card_insert_of_notMem h_not_mem1, card_singleton]
  have h_sum : ({p * q, q, p, 1} : Finset ℕ).sum (fun d => d * (Nat.divisors d).card) = 4 * (p * q) + 2 * q + 2 * p + 1 := by
    rw [sum_insert h_not_mem3, sum_insert h_not_mem2, sum_insert h_not_mem1, sum_singleton]
    rw [h_tau_1, h_tau_p, h_tau_q, h_tau_pq]
    ring
  rw [h_card, h_sum]
  omega
