import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 500000
set_option maxHeartbeats 2000000
open Nat
open scoped ArithmeticFunction.sigma

lemma sum_sigma_le_sigma_sq_strong (n : ℕ) (hn12 : n > 12) (h_not_prime : ¬ n.Prime) :
    (n : ℤ) * ∑ c ∈ divisors n, (σ 1 c : ℤ) ≤ (σ 1 n : ℤ) * (σ 1 n : ℤ) - 2 * (σ 1 n : ℤ) + 2 * (n : ℤ) + 1 := by sorry

def a (n : ℕ) : ℤ :=
  (divisors n).sum fun d =>
    (2 * d : ℤ) - (ArithmeticFunction.sigma 1 d : ℤ)

lemma a_eq_formula (n : ℕ) : a n = 2 * (σ 1 n : ℤ) - ∑ d ∈ divisors n, (σ 1 d : ℤ) := by sorry

lemma sigma_ge_two_n_plus_two (n : ℕ) (hn12 : n > 12) (h_not_prime : ¬ n.Prime) (h_ab : (σ 1 n : ℤ) > 2 * (n : ℤ)) (ha1 : a n = 1) :
    (σ 1 n : ℤ) ≥ 2 * (n : ℤ) + 2 := by
  have hn0 : n > 0 := by omega
  have h_le := sum_sigma_le_sigma_sq_strong n hn12 h_not_prime
  have h_a := a_eq_formula n
  have h_mul_a : (n : ℤ) * a n = 2 * (n : ℤ) * (σ 1 n : ℤ) - (n : ℤ) * ∑ c ∈ divisors n, (σ 1 c : ℤ) := by
    rw [h_a, mul_sub, ← mul_assoc]
    ring
  rw [ha1, mul_one] at h_mul_a
  have h_quad : (σ 1 n : ℤ) * (σ 1 n : ℤ) - 2 * ((n : ℤ) + 1) * (σ 1 n : ℤ) + 3 * (n : ℤ) + 1 ≥ 0 := by
    nlinarith [h_le, h_mul_a]
  have h_cases : (σ 1 n : ℤ) = 2 * (n : ℤ) + 1 ∨ (σ 1 n : ℤ) ≥ 2 * (n : ℤ) + 2 := by
    omega
  rcases h_cases with h_eq | h_ge
  · rw [h_eq] at h_quad
    have h_neg : (2 * (n : ℤ) + 1) * (2 * (n : ℤ) + 1) - 2 * ((n : ℤ) + 1) * (2 * (n : ℤ) + 1) + 3 * (n : ℤ) + 1 = (n : ℤ) := by
      ring
    rw [h_neg] at h_quad
    rw [h_eq]
    clear h_le h_mul_a h_eq h_ab h_quad h_a ha1 h_not_prime hn0
    omega
  · exact h_ge
