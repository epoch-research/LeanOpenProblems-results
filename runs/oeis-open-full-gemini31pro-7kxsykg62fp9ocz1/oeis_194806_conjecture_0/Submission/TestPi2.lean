import Mathlib

open Nat Finset

lemma centralBinom_le_pow_pi (n : ℕ) (hn : 0 < n) : centralBinom n ≤ (2 * n) ^ (primeCounting (2 * n)) := by
  have H1 : centralBinom n = ∏ p ∈ filter Nat.Prime (range (2 * n + 1)), p ^ (centralBinom n).factorization p := by
    calc centralBinom n = ∏ p ∈ range (2 * n + 1), p ^ (centralBinom n).factorization p := n.prod_pow_factorization_centralBinom.symm
    _ = ∏ p ∈ filter Nat.Prime (range (2 * n + 1)), p ^ (centralBinom n).factorization p := by
      symm
      apply prod_filter_of_ne
      intro p _ hp
      contrapose! hp
      rw [factorization_eq_zero_of_not_prime (centralBinom n) hp]
      exact pow_zero p
  have H2 : ∏ p ∈ filter Nat.Prime (range (2 * n + 1)), p ^ (centralBinom n).factorization p ≤ ∏ p ∈ filter Nat.Prime (range (2 * n + 1)), (2 * n) := by
    apply prod_le_prod
    · intro p _
      exact Nat.zero_le _
    · intro p hp
      exact pow_factorization_choose_le (mul_pos two_pos hn)
  have H3 : ∏ p ∈ filter Nat.Prime (range (2 * n + 1)), (2 * n) = (2 * n) ^ (filter Nat.Prime (range (2 * n + 1))).card := by
    exact prod_const (2 * n)
  have H4 : (filter Nat.Prime (range (2 * n + 1))).card = primeCounting (2 * n) := by
    rw [primeCounting, primeCounting', count_eq_card_filter_range]
  calc centralBinom n = ∏ p ∈ filter Nat.Prime (range (2 * n + 1)), p ^ (centralBinom n).factorization p := H1
    _ ≤ ∏ p ∈ filter Nat.Prime (range (2 * n + 1)), (2 * n) := H2
    _ = (2 * n) ^ (filter Nat.Prime (range (2 * n + 1))).card := H3
    _ = (2 * n) ^ (primeCounting (2 * n)) := by rw [H4]
