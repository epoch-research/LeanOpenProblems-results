import Submission.TestHugeSum2
import FormalConjectures.Util.ProblemImports
open Finset Nat Polynomial

lemma inner_sum_eval (n j : ℕ) :
  ∑ v ∈ range (2 * j + 1), ( (n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ v ) =
  (n.choose j : ℤ) * (-1 : ℤ) ^ j := by
  have h_poly : (1 - X : ℤ[X]) ^ n * (1 + X : ℤ[X]) ^ n = (1 - X ^ 2) ^ n := by
    calc (1 - X : ℤ[X]) ^ n * (1 + X : ℤ[X]) ^ n = ((1 - X) * (1 + X)) ^ n := (mul_pow (1 - X : ℤ[X]) (1 + X) n).symm
      _ = (1 - X ^ 2) ^ n := by ring_nf
  have LHS : coeff ((1 - X : ℤ[X]) ^ n * (1 + X : ℤ[X]) ^ n) (2 * j) =
             ∑ v ∈ range (2 * j + 1), ( (-1 : ℤ) ^ v * (n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) ) := by
    rw [coeff_mul]
    have h_sum : ∑ x ∈ antidiagonal (2 * j), coeff ((1 - X : ℤ[X]) ^ n) x.1 * coeff ((1 + X : ℤ[X]) ^ n) x.2 =
                 ∑ v ∈ range (2 * j + 1), coeff ((1 - X : ℤ[X]) ^ n) v * coeff ((1 + X : ℤ[X]) ^ n) (2 * j - v) := by
      exact sum_antidiagonal_eq_sum_range_succ (fun k l => coeff ((1 - X : ℤ[X]) ^ n) k * coeff ((1 + X : ℤ[X]) ^ n) l) (2 * j)
    rw [h_sum]
    apply sum_congr rfl
    intro v _
    have h1 : coeff ((1 - X : ℤ[X]) ^ n) v = (-1 : ℤ) ^ v * (n.choose v : ℤ) := coeff_one_sub_X_pow n v
-- coeff_one_sub_X_pow n v
    have h2 : coeff ((1 + X : ℤ[X]) ^ n) (2 * j - v) = (n.choose (2 * j - v) : ℤ) := Polynomial.coeff_one_add_X_pow ℤ n (2 * j - v)
    rw [h1, h2]
  have RHS : coeff ((1 - X ^ 2 : ℤ[X]) ^ n) (2 * j) = (-1 : ℤ) ^ j * (n.choose j : ℤ) := by
    have h_sub : (1 - X ^ 2 : ℤ[X]) = - X ^ 2 + 1 := by ring
    rw [h_sub]
    have h_pow := add_pow (- X ^ 2 : ℤ[X]) 1 n
    rw [h_pow]
    simp only [one_pow, mul_one]
    rw [finset_sum_coeff]
    have h_term : ∀ m, coeff ((- X ^ 2 : ℤ[X]) ^ m * (n.choose m : ℤ[X])) (2 * j) = if m = j then ((-1 : ℤ) ^ m * (n.choose m : ℤ)) else 0 := by
      intro m
      have hc : (- X ^ 2 : ℤ[X]) ^ m * (n.choose m : ℤ[X]) = C ((-1 : ℤ) ^ m * (n.choose m : ℤ)) * (X : ℤ[X]) ^ (2 * m) := by
        calc (- X ^ 2 : ℤ[X]) ^ m * (n.choose m : ℤ[X]) = (-1 * X ^ 2 : ℤ[X]) ^ m * (n.choose m : ℤ[X]) := by ring_nf
          _ = (-1 : ℤ[X]) ^ m * (X ^ 2 : ℤ[X]) ^ m * (n.choose m : ℤ[X]) := by rw [mul_pow]
          _ = C ((-1 : ℤ) ^ m) * (X : ℤ[X]) ^ (2 * m) * C (n.choose m : ℤ) := by
            have h1 : (-1 : ℤ[X]) = C (-1 : ℤ) := by simp
            have h2 : (n.choose m : ℤ[X]) = C (n.choose m : ℤ) := by rfl
            have h3 : (X ^ 2 : ℤ[X]) ^ m = (X : ℤ[X]) ^ (2 * m) := by rw [← pow_mul]
            rw [h1, h2, map_pow, h3]
          _ = C ((-1 : ℤ) ^ m * (n.choose m : ℤ)) * (X : ℤ[X]) ^ (2 * m) := by
            rw [map_mul]
            ring
      rw [hc, coeff_C_mul_X_pow]
      by_cases hm : m = j
      · subst hm
        rw [if_pos rfl, if_pos rfl]
      · have h_not : ¬ 2 * j = 2 * m := by intro contra; exact hm (by omega)
        rw [if_neg hm, if_neg h_not]
    have h_sum : ∑ m ∈ range (n + 1), coeff ((- X ^ 2 : ℤ[X]) ^ m * (n.choose m : ℤ[X])) (2 * j) = ∑ m ∈ range (n + 1), (if m = j then ((-1 : ℤ) ^ m * (n.choose m : ℤ)) else 0) := sum_congr rfl (fun m _ => h_term m)
    rw [h_sum, sum_ite_eq']
    by_cases hj : j ∈ range (n + 1)
    · rw [if_pos hj]
    · rw [if_neg hj]
      have hn : n < j := by have h1 := mem_range.not.1 hj; omega
      have h_zero : n.choose j = 0 := choose_eq_zero_of_lt hn
      rw [h_zero]
      simp
  have h_eq : ∑ v ∈ range (2 * j + 1), (n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ v =
              ∑ v ∈ range (2 * j + 1), (-1 : ℤ) ^ v * (n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) := by
    apply sum_congr rfl
    intro v _
    ring
  rw [h_eq, ← LHS, h_poly, RHS]
  ring


