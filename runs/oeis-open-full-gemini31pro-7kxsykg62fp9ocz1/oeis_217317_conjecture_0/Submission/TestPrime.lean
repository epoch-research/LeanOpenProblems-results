import Mathlib.Data.Nat.Prime.Basic

lemma test_not_prime : ¬ Nat.Prime 15 := by
  have h : 15 = 3 * 5 := rfl
  rw [h]
  apply Nat.not_prime_mul <;> decide
