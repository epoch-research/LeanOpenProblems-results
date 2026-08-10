import FormalConjectures.Util.ProblemImports
import Mathlib.NumberTheory.Bernoulli

open Nat Finset BigOperators

lemma sum_range_sq_eq (p : ℕ) : (∑ k ∈ range p, (k : ℚ) ^ 2) = (p : ℚ) * (p - 1) * (2 * p - 1) / 6 := by
  have h := sum_range_pow p 2
  simp only [sum_range_succ, sum_range_zero, zero_add] at h
  rw [bernoulli_zero, bernoulli_one, bernoulli_two] at h
  -- Now simplify binomial coefficients and powers
  -- (2+1).choose 0 = 1, (2+1).choose 1 = 3, (2+1).choose 2 = 3
  -- We can just do dec_trivial or similar, or simp
  simp only [Nat.choose, Nat.choose_succ_succ] at h
  -- Let's see if ring can do it
  rw [h]
  ring
