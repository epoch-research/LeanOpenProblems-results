import Submission.Spec
import Mathlib
open Nat Finset


lemma a_pq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) : a (p * q) = 1 + 2 * p + 2 * q := by
  have h_divs : (p * q).divisors = {1, p, q, p * q} := sorry
  have h_taupq : (Nat.divisors (p * q)).card = 4 := sorry
  have h_taup : (Nat.divisors p).card = 2 := sorry
  have h_tauq : (Nat.divisors q).card = 2 := sorry
  have h_tau1 : (Nat.divisors 1).card = 1 := rfl
  unfold a
  change (p * q).divisors.sum (fun d => d * (Nat.divisors d).card) - (p * q) * (p * q).divisors.card = 1 + 2 * p + 2 * q
  rw [h_divs, h_taupq]
  have h_sum : ({1, p, q, p * q} : Finset ℕ).sum (fun d => d * (Nat.divisors d).card) = 1 + 2 * p + 2 * q + 4 * (p * q) := sorry
  rw [h_sum]
  omega
