import Submission.Spec
import Mathlib.Data.Finset.Basic

open Nat ArithmeticFunction

theorem a8_val : a 8 = 25584 := by
  have d8 : Nat.divisors 8 = {1, 2, 4, 8} := by decide
  have m1 : moebius 1 = 1 := moebius_apply_one
  have m2 : moebius 2 = -1 := moebius_apply_prime Nat.prime_two
  have m4 : moebius 4 = 0 := moebius_eq_zero_of_not_squarefree (by decide)
  have m8 : moebius 8 = 0 := moebius_eq_zero_of_not_squarefree (by decide)
  dsimp [a]
  rw [d8]
  simp [m1, m2, m4, m8, harmonic]
  norm_num

theorem cf8 : cardFactors 8 = 3 := by
  have h8 : 8 = 2 ^ 3 := by decide
  rw [h8]
  exact cardFactors_apply_prime_pow Nat.prime_two

theorem disproof_check : ¬ (∀ (n : ℕ) (hn : n > 0), a n < 0 ↔ Odd (cardFactors n) ∧ cardFactors n ≥ 3) := by
  intro h
  have h8 : a 8 < 0 ↔ Odd (cardFactors 8) ∧ cardFactors 8 ≥ 3 := h 8 (by decide)
  rw [a8_val, cf8] at h8
  revert h8
  decide
