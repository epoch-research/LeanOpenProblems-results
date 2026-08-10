import FormalConjectures.Util.ProblemImports

open Polynomial Finset Nat
open scoped BigOperators

/-- Coefficient of the Legendre cubic power in terms of the Deuring/Hasse polynomial. -/
lemma coeff_legendre_cubic_aux (n : ℕ) {R : Type*} [CommRing R] (lam : R) :
    (((X : R[X]) - 1) ^ n * ((X : R[X]) - C lam) ^ n).coeff n =
      (-1 : R) ^ n * (∑ k ∈ range (n + 1), ((n.choose k : ℕ) : R) ^ 2 * lam ^ k) := by
  rw [coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => (((X : R[X]) - 1) ^ n).coeff a * (((X : R[X]) - C lam) ^ n).coeff b) n]
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  have hk_le : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hk)
  have hleft : (((X : R[X]) - 1) ^ n).coeff k = (-1 : R) ^ (n - k) * (n.choose k : R) := by
    simpa [sub_eq_add_neg] using (coeff_X_add_C_pow (-1 : R) n k)
  have hright : (((X : R[X]) - C lam) ^ n).coeff (n - k) = (-lam) ^ k * (n.choose (n - k) : R) := by
    have h := coeff_X_add_C_pow (-lam : R) n (n - k)
    have h1 : n - (n - k) = k := by omega
    simpa [sub_eq_add_neg, h1] using h
  rw [hleft, hright]
  have hchoose : n.choose (n - k) = n.choose k := by
    rw [Nat.choose_symm hk_le]
  rw [hchoose]
  have hnegpow : (-lam) ^ k = (-1 : R) ^ k * lam ^ k := by
    rw [show (-lam) = (-1 : R) * lam by ring, mul_pow]
  rw [hnegpow]
  calc
    ((-1 : R) ^ (n - k) * ↑(n.choose k)) * (((-1 : R) ^ k * lam ^ k) * ↑(n.choose k))
        = ((-1 : R) ^ (n - k) * (-1 : R) ^ k) * (((n.choose k : ℕ) : R) ^ 2 * lam ^ k) := by ring
    _ = (-1 : R) ^ n * (((n.choose k : ℕ) : R) ^ 2 * lam ^ k) := by
        rw [← pow_add]
        have hadd : n - k + k = n := by omega
        rw [hadd]

lemma coeff_legendre_cubic_pow_eq_sum (n : ℕ) {R : Type*} [CommRing R] (lam : R) :
    (((X : R[X]) * ((X : R[X]) - 1) * ((X : R[X]) - C lam)) ^ n).coeff (2 * n) =
      (-1 : R) ^ n * (∑ k ∈ range (n + 1), ((n.choose k : ℕ) : R) ^ 2 * lam ^ k) := by
  rw [mul_assoc, mul_pow]
  rw [mul_pow]
  rw [coeff_X_pow_mul']
  rw [if_pos (by omega : n ≤ 2 * n)]
  have hsub : 2 * n - n = n := by omega
  rw [hsub]
  exact coeff_legendre_cubic_aux n lam
