import Submission.Spec
import Mathlib

open Nat Finset


lemma a_p2 (p : ℕ) (hp : p.Prime) : a (p ^ 2) = 1 + 2 * p := by
  have h_divs : (p ^ 2).divisors = {p ^ 2, p, 1} := hp.divisors_sq
  have h_ne1 : p ≠ p ^ 2 := by have := hp.two_le; nlinarith
  have h_ne2 : 1 ≠ p ^ 2 := by have := hp.two_le; nlinarith
  have h_ne3 : 1 ≠ p := by have := hp.two_le; omega
  have h_not_mem1 : p ∉ ({1} : Finset ℕ) := by rw [mem_singleton]; exact h_ne3.symm
  have h_not_mem2 : p ^ 2 ∉ ({p, 1} : Finset ℕ) := by
    rw [mem_insert, mem_singleton]
    push_neg
    exact ⟨h_ne1.symm, h_ne2.symm⟩
  have h_tau_p2 : (Nat.divisors (p ^ 2)).card = 3 := by
    rw [h_divs, card_insert_of_notMem h_not_mem2, card_insert_of_notMem h_not_mem1, card_singleton]
  have h_not_mem3 : p ∉ ({1} : Finset ℕ) := h_not_mem1
  have h_tau_p : (Nat.divisors p).card = 2 := by
    -- wait, hp.divisors is {1, p}. But we can use {p, 1} if we rewrite it.
    -- Nat.Prime.divisors hp is {1, p}
    have : p.divisors = {p, 1} := by
      ext x
      rw [hp.divisors, mem_insert, mem_insert, mem_singleton, mem_singleton]
      tauto
    rw [this, card_insert_of_notMem h_not_mem3, card_singleton]
  have h_tau_1 : (Nat.divisors 1).card = 1 := rfl
  unfold a
  change (p ^ 2).divisors.sum (fun d => d * (Nat.divisors d).card) - (p ^ 2) * (p ^ 2).divisors.card = 1 + 2 * p
  rw [h_divs]
  have h_card : ({p ^ 2, p, 1} : Finset ℕ).card = 3 := by
    exact card_insert_of_notMem h_not_mem2 |>.trans (by rw [card_insert_of_notMem h_not_mem1, card_singleton])
  have h_sum : ({p ^ 2, p, 1} : Finset ℕ).sum (fun d => d * (Nat.divisors d).card) = 3 * (p ^ 2) + 2 * p + 1 := by
    rw [sum_insert h_not_mem2, sum_insert h_not_mem1, sum_singleton]
    rw [h_tau_1, h_tau_p, h_tau_p2]
    ring
  rw [h_card, h_sum]
  omega
