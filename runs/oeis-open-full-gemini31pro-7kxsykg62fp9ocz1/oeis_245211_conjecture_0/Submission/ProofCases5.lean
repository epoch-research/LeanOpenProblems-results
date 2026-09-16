import Submission.Spec
import Mathlib

open Nat Finset


lemma a_pk (p k : ℕ) (hp : p.Prime) :
  a (p ^ k) = ∑ j ∈ range k, (j + 1) * p ^ j := by
  unfold a
  have h_divs := Nat.divisors_prime_pow hp k
  change (p ^ k).divisors.sum (fun d => d * (Nat.divisors d).card) - (p ^ k) * (Nat.divisors (p ^ k)).card = _
  have h_tau_pk : (Nat.divisors (p ^ k)).card = k + 1 := by
    rw [Nat.divisors_prime_pow hp k, card_map, card_range]
  rw [h_tau_pk, h_divs, sum_map]
  have h_sum : (∑ j ∈ range (k + 1), (p ^ j) * (Nat.divisors (p ^ j)).card) =
    ∑ j ∈ range (k + 1), (j + 1) * p ^ j := by
    apply sum_congr rfl
    intro j hj
    have h_tau : (Nat.divisors (p ^ j)).card = j + 1 := by
      rw [Nat.divisors_prime_pow hp j, card_map, card_range]
    rw [h_tau]
    ring
  change (∑ j ∈ range (k + 1), (p ^ j) * (Nat.divisors (p ^ j)).card) - (p ^ k) * (k + 1) = _
  rw [h_sum]
  have h_split : ∑ j ∈ range (k + 1), (j + 1) * p ^ j = (∑ j ∈ range k, (j + 1) * p ^ j) + (k + 1) * p ^ k := by
    exact sum_range_succ (fun j => (j + 1) * p ^ j) k
  rw [h_split]
  have : (p ^ k) * (k + 1) = (k + 1) * p ^ k := mul_comm _ _
  rw [this]
  exact Nat.add_sub_cancel _ _
