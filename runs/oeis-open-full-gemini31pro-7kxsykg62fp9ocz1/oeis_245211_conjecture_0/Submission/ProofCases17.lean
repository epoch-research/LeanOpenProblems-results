import Submission.Spec
import Mathlib
import Submission.ProofCases12

open Nat Finset

lemma a_ge_two_primes {n p q : ℕ} (hn_pos : 0 < n) (hp : p.Prime) (hq : q.Prime)
  (h1 : p ≠ q) (hdp : p ∣ n) (hdq : q ∣ n)
  (h_tau_p : 4 ≤ (Nat.divisors (n / p)).card)
  (h_tau_q : 3 ≤ (Nat.divisors (n / q)).card) :
  4 * (n / p) + 3 * (n / q) ≤ a n := by
  have hd_p : n / p ∈ n.divisors.erase n := a_ge_three_primes_step hn_pos hp hdp
  have hd_q : n / q ∈ n.divisors.erase n := a_ge_three_primes_step hn_pos hq hdq
  have hpq_ne : n / p ≠ n / q := a_ge_three_primes_ne hn_pos hdp hdq h1
  have h_sub : {n / p, n / q} ⊆ n.divisors.erase n := by
    intro d hd
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact hd_p
    · exact hd_q
  rw [a_eq_sum_proper hn_pos]
  have h_sum : ({n / p, n / q} : Finset ℕ).sum (fun d => d * (Nat.divisors d).card) ≤ ∑ d ∈ n.divisors.erase n, d * (Nat.divisors d).card := by
    exact sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => Nat.zero_le _)
  have h_eval : ({n / p, n / q} : Finset ℕ).sum (fun d => d * (Nat.divisors d).card) = 
    (n / p) * (Nat.divisors (n / p)).card + (n / q) * (Nat.divisors (n / q)).card := by
    rw [sum_insert, sum_singleton]
    simp only [mem_singleton]
    exact hpq_ne
  rw [h_eval] at h_sum
  calc 4 * (n / p) + 3 * (n / q) ≤ (n / p) * 4 + (n / q) * 3 := by ring_nf; rfl
    _ ≤ (n / p) * (Nat.divisors (n / p)).card + (n / q) * (Nat.divisors (n / q)).card := by gcongr
    _ ≤ ∑ d ∈ n.divisors.erase n, d * (Nat.divisors d).card := h_sum

