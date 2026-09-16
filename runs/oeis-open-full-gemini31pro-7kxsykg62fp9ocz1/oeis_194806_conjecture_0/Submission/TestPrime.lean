import Mathlib

open Nat Finset

lemma centralBinom_le_pow_pi (n : ℕ) (hn : 0 < n) : centralBinom n ≤ (2 * n) ^ (primeCounting (2 * n)) := by
  have H1 : centralBinom n = ∏ p ∈ filter Prime (range (2 * n + 1)), p ^ (centralBinom n).factorization p := by
    sorry
  have H2 : ∏ p ∈ filter Prime (range (2 * n + 1)), p ^ (centralBinom n).factorization p ≤ ∏ p ∈ filter Prime (range (2 * n + 1)), (2 * n) := by
    apply prod_le_prod
    · intro p _
      exact zero_le _
    · intro p hp
      sorry -- pow_factorization_choose_le
  have H3 : ∏ p ∈ filter Prime (range (2 * n + 1)), (2 * n) = (2 * n) ^ (filter Prime (range (2 * n + 1))).card := by
    exact prod_const (2 * n)
  sorry
