import Mathlib
import Submission.ProofCases3
import Submission.ProofCases18

open Nat Finset

lemma bound_sigma_div_n_2_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
  ∑ d ∈ (p * q).divisors, (1 / (d : ℚ)) = (1 + 1 / (p : ℚ)) * (1 + 1 / (q : ℚ)) := by
  have hd : (p * q).divisors = {p * q, q, p, 1} := divisors_pq hp hq hpq
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
    
  rw [hd, sum_insert h_not_mem3, sum_insert h_not_mem2, sum_insert h_not_mem1, sum_singleton]
  have hp_cast : ((p * q : ℕ) : ℚ) = (p : ℚ) * (q : ℚ) := by exact_mod_cast rfl
  rw [hp_cast, one_div, mul_inv, ← one_div, ← one_div]
  ring
