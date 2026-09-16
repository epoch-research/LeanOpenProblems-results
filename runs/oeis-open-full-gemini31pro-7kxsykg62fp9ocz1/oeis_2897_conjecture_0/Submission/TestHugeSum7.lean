import FormalConjectures.Util.ProblemImports
open Finset Nat Polynomial

lemma sum_choose_square (n : ℕ) :
  ∑ j ∈ range (n + 1), (n.choose j : ℤ) ^ 2 = ((2 * n).choose n : ℤ) := by
  have h_poly : (1 + X : ℤ[X]) ^ n * (1 + X : ℤ[X]) ^ n = (1 + X) ^ (2 * n) := by
    rw [← pow_add]
    have h2 : n + n = 2 * n := by omega
    rw [h2]
  have LHS : coeff ((1 + X : ℤ[X]) ^ n * (1 + X : ℤ[X]) ^ n) n =
             ∑ j ∈ range (n + 1), (n.choose j : ℤ) ^ 2 := by
    rw [coeff_mul]
    have h_sum : ∑ x ∈ antidiagonal n, coeff ((1 + X : ℤ[X]) ^ n) x.1 * coeff ((1 + X : ℤ[X]) ^ n) x.2 =
                 ∑ j ∈ range (n + 1), coeff ((1 + X : ℤ[X]) ^ n) j * coeff ((1 + X : ℤ[X]) ^ n) (n - j) := by
      exact sum_antidiagonal_eq_sum_range_succ (fun k l => coeff ((1 + X : ℤ[X]) ^ n) k * coeff ((1 + X : ℤ[X]) ^ n) l) n
    rw [h_sum]
    apply sum_congr rfl
    intro j hj
    have h1 : coeff ((1 + X : ℤ[X]) ^ n) j = (n.choose j : ℤ) := Polynomial.coeff_one_add_X_pow ℤ n j
    have h2 : coeff ((1 + X : ℤ[X]) ^ n) (n - j) = (n.choose (n - j) : ℤ) := Polynomial.coeff_one_add_X_pow ℤ n (n - j)
    rw [h1, h2]
    have hj_le : j ≤ n := by
      have h1 := mem_range.1 hj
      omega
    have h_symm : n.choose (n - j) = n.choose j := choose_symm hj_le
    rw [h_symm]
    ring
  have RHS : coeff ((1 + X : ℤ[X]) ^ (2 * n)) n = ((2 * n).choose n : ℤ) := by
    exact Polynomial.coeff_one_add_X_pow ℤ (2 * n) n
  rw [← LHS, h_poly, RHS]


