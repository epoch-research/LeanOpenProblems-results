import Mathlib

def my_is_prime (p : ℕ) : Bool :=
  p == 2 || p == 3 || p == 5 || p == 7 || p == 11 || p == 13 || p == 17

lemma my_is_prime_eq_prime (p : ℕ) (h : my_is_prime p = true) : p.Prime := by
  have h_bound : p < 18 := by
    by_contra h_ge
    have h_not_lt : ¬(p < 18) := h_ge
    have h_false : my_is_prime p = false := by
      unfold my_is_prime
      have h1 : p ≠ 2 := by omega
      have h2 : p ≠ 3 := by omega
      have h3 : p ≠ 5 := by omega
      have h4 : p ≠ 7 := by omega
      have h5 : p ≠ 11 := by omega
      have h6 : p ≠ 13 := by omega
      have h7 : p ≠ 17 := by omega
      simp [h1, h2, h3, h4, h5, h6, h7]
    rw [h] at h_false
    contradiction
  have H : ∀ (x : ℕ), x < 18 → my_is_prime x = true → x.Prime := by decide
  exact H p h_bound h
