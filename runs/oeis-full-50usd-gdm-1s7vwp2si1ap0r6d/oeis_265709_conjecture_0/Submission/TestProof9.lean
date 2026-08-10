import FormalConjectures.Util.ProblemImports

open Nat Finset ArithmeticFunction

lemma sum_pow_pair (p : ℕ) (k : ℕ) :
  ∑ x ∈ range (2*k + 2), p^x = (p + 1) * ∑ i ∈ range (k + 1), p^(2*i) := by
  induction k with
  | zero =>
    simp [sum_range_succ]
    omega
  | succ k ih =>
    have h1 : 2*(k+1) + 2 = 2*k + 2 + 2 := by omega
    rw [h1]
    rw [sum_range_add]
    rw [ih]
    have h2 : ∑ x ∈ range 2, p ^ (2 * k + 2 + x) = p^(2*k + 2) + p^(2*k + 3) := by
      rw [sum_range_succ, sum_range_one]
      rfl
    rw [h2]
    have h3 : p^(2*k + 2) + p^(2*k + 3) = (p + 1) * p^(2*k + 2) := by
      have h_pow : p^(2*k + 3) = p^(2*k + 2) * p := by
        have h_eq : 2*k + 3 = (2*k + 2) + 1 := by omega
        rw [h_eq, pow_succ]
      rw [h_pow]
      ring
    rw [h3]
    rw [← mul_add]
    have h4 : ∑ i ∈ range (k + 2), p ^ (2 * i) = (∑ i ∈ range (k + 1), p ^ (2 * i)) + p^(2*k + 2) := by
      rw [sum_range_succ]
      have : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [this]
    rw [h4]
