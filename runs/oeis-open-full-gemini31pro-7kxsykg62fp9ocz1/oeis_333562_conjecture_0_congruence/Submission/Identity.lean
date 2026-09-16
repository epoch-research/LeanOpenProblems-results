import Mathlib
import Submission.Spec

open Nat Finset

lemma my_geom_sum {R : Type*} [CommRing R] (Y : R) (n : ℕ) :
    (∑ k ∈ range n, (1 - Y) * Y^k) = 1 - Y^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    ring

lemma binomial_telescoping {R : Type*} [CommRing R] (Y : R) (n M : ℕ) :
    ((n + M).choose (M + 1) : R) * Y^n + (1 - Y) * ∑ k ∈ range n, ((M + 1 + k).choose k : R) * Y^k
    = ∑ k ∈ range n, ((M + k).choose k : R) * Y^k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ]
    calc
      ((n + 1 + M).choose (M + 1) : R) * Y^(n + 1) + (1 - Y) * ((∑ k ∈ range n, ((M + 1 + k).choose k : R) * Y^k) + ((M + 1 + n).choose n : R) * Y^n)
      _ = (((n + 1 + M).choose (M + 1) : R) * Y^(n + 1) + (1 - Y) * ((M + 1 + n).choose n : R) * Y^n - ((n + M).choose (M + 1) : R) * Y^n) + (((n + M).choose (M + 1) : R) * Y^n + (1 - Y) * ∑ k ∈ range n, ((M + 1 + k).choose k : R) * Y^k) := by ring
      _ = (((n + 1 + M).choose (M + 1) : R) * Y^(n + 1) + (1 - Y) * ((M + 1 + n).choose n : R) * Y^n - ((n + M).choose (M + 1) : R) * Y^n) + (∑ k ∈ range n, ((M + k).choose k : R) * Y^k) := by rw [ih]
      _ = ((M + n).choose n : R) * Y^n + (∑ k ∈ range n, ((M + k).choose k : R) * Y^k) := by
        have h1 : (M + 1 + n).choose n = (n + 1 + M).choose (M + 1) := by
          have h_eq1 : M + 1 + n = n + 1 + M := by omega
          rw [h_eq1]
          have h_symm := choose_symm (show n ≤ n + 1 + M by omega)
          have h_sub : n + 1 + M - n = M + 1 := by omega
          rw [h_sub] at h_symm
          exact h_symm.symm
        have h2 : (n + 1 + M).choose (M + 1) = (n + M).choose (M + 1) + (n + M).choose M := by
          have h_eq : n + 1 + M = n + M + 1 := by omega
          rw [h_eq, choose_succ_succ (n + M) M, add_comm]
        have h3 : (n + M).choose M = (M + n).choose n := by
          have h_eq : n + M = M + n := by omega
          rw [h_eq]
          have h_symm := choose_symm (show M ≤ M + n by omega)
          have h_sub : M + n - M = n := by omega
          rw [h_sub] at h_symm
          exact h_symm.symm
        have h_cast : (((n + 1 + M).choose (M + 1) : R) * Y^(n + 1) + (1 - Y) * ((M + 1 + n).choose n : R) * Y^n - ((n + M).choose (M + 1) : R) * Y^n) =
                      ((n + 1 + M).choose (M + 1) : R) * Y^(n + 1) + ((M + 1 + n).choose n : R) * Y^n - ((M + 1 + n).choose n : R) * Y^(n + 1) - ((n + M).choose (M + 1) : R) * Y^n := by ring
        rw [h_cast, h1]
        have h_cast2 : ((n + 1 + M).choose (M + 1) : R) * Y ^ (n + 1) + ((n + 1 + M).choose (M + 1) : R) * Y ^ n - ((n + 1 + M).choose (M + 1) : R) * Y ^ (n + 1) - ((n + M).choose (M + 1) : R) * Y ^ n =
                       (((n + 1 + M).choose (M + 1) : R) - ((n + M).choose (M + 1) : R)) * Y^n := by ring
        rw [h_cast2]
        have h_cast3 : (((n + 1 + M).choose (M + 1) : R) - ((n + M).choose (M + 1) : R)) = ((n + M).choose M : R) := by
          rw [h2]
          push_cast
          ring
        rw [h_cast3, h3]
      _ = (∑ k ∈ range n, ((M + k).choose k : R) * Y^k) + ((M + n).choose n : R) * Y^n := by ring

theorem binomial_identity {R : Type*} [CommRing R] (X : R) (n M : ℕ) :
    (∑ j ∈ range (M + 1), ((n + j - 1).choose j : R) * X^j * (1 - X)^n) +
    (∑ k ∈ range n, ((M + k).choose k : R) * X^(M + 1) * (1 - X)^k) = 1 := by
  induction M with
  | zero =>
    have h := my_geom_sum (1 - X) n
    have h1 : 1 - (1 - X) = X := by ring
    rw [h1] at h
    have h2 : (∑ j ∈ range (0 + 1), ((n + j - 1).choose j : R) * X^j * (1 - X)^n) = (1 - X)^n := by
      simp
    have h3 : (∑ k ∈ range n, ((0 + k).choose k : R) * X^(0 + 1) * (1 - X)^k) = 1 - (1 - X)^n := by
      calc
        _ = ∑ k ∈ range n, 1 * X^1 * (1 - X)^k := by
          apply sum_congr rfl
          intro x _
          simp
        _ = ∑ k ∈ range n, X * (1 - X)^k := by
          apply sum_congr rfl
          intro x _
          ring
        _ = 1 - (1 - X)^n := h
    rw [h2, h3]
    ring
  | succ M ih =>
    rw [sum_range_succ]
    -- LHS is S1(M) + ((n + M).choose (M + 1)) * X^{M+1} * (1 - X)^n + S2(M+1)
    have h_tel := binomial_telescoping (1 - X) n M
    have h_sub : 1 - (1 - X) = X := by ring
    rw [h_sub] at h_tel
    calc
      (∑ j ∈ range (M + 1), ↑((n + j - 1).choose j) * X ^ j * (1 - X) ^ n) + ↑((n + M).choose (M + 1)) * X ^ (M + 1) * (1 - X) ^ n + ∑ k ∈ range n, ↑((M + 1 + k).choose k) * X ^ (M + 1 + 1) * (1 - X) ^ k
      _ = (∑ j ∈ range (M + 1), ↑((n + j - 1).choose j) * X ^ j * (1 - X) ^ n) + X ^ (M + 1) * (↑((n + M).choose (M + 1)) * (1 - X) ^ n + X * ∑ k ∈ range n, ↑((M + 1 + k).choose k) * (1 - X) ^ k) := by
        have h_sum1 : ∑ k ∈ range n, ↑((M + 1 + k).choose k) * X ^ (M + 1 + 1) * (1 - X) ^ k = ∑ k ∈ range n, X ^ (M + 1) * X * ↑((M + 1 + k).choose k) * (1 - X) ^ k := by
          apply sum_congr rfl
          intro x _
          ring
        rw [h_sum1]
        have h_sum2 : (∑ k ∈ range n, X ^ (M + 1) * X * ↑((M + 1 + k).choose k) * (1 - X) ^ k) = X ^ (M + 1) * ∑ k ∈ range n, X * ↑((M + 1 + k).choose k) * (1 - X) ^ k := by
          rw [mul_sum]
          apply sum_congr rfl
          intro x _
          ring
        rw [h_sum2]
        have h_sum3 : (∑ k ∈ range n, X * ↑((M + 1 + k).choose k) * (1 - X) ^ k) = X * ∑ k ∈ range n, ↑((M + 1 + k).choose k) * (1 - X) ^ k := by
          rw [mul_sum]
          apply sum_congr rfl
          intro x _
          ring
        rw [h_sum3]
        ring
      _ = (∑ j ∈ range (M + 1), ↑((n + j - 1).choose j) * X ^ j * (1 - X) ^ n) + X ^ (M + 1) * (∑ k ∈ range n, ↑((M + k).choose k) * (1 - X) ^ k) := by rw [h_tel]
      _ = (∑ j ∈ range (M + 1), ↑((n + j - 1).choose j) * X ^ j * (1 - X) ^ n) + ∑ k ∈ range n, ↑((M + k).choose k) * X ^ (M + 1) * (1 - X) ^ k := by
        have h_sum2 : ∑ k ∈ range n, ↑((M + k).choose k) * X ^ (M + 1) * (1 - X) ^ k = X ^ (M + 1) * ∑ k ∈ range n, ↑((M + k).choose k) * (1 - X) ^ k := by
          rw [mul_sum]
          apply sum_congr rfl
          intro x _
          ring
        rw [h_sum2]
      _ = 1 := ih


def a_z (n : ℕ) : ℤ :=
  ∑ j ∈ range (3 * n + 1), ((n + j - 1).choose j : ℤ) * (2 : ℤ) ^ j

def S (n : ℕ) : ℤ :=
  ∑ k ∈ range n, ((3 * n + k).choose k : ℤ) * (-1) ^ k

lemma a_z_eq_S (n : ℕ) : a_z n = (-1) ^ n * (1 - 2 ^ (3 * n + 1) * S n) := by
  have h := binomial_identity (2 : ℤ) n (3 * n)
  have h_sub : (1 - (2 : ℤ)) = -1 := by ring
  rw [h_sub] at h
  -- h : (∑ j ∈ range (3 * n + 1), ↑((n + j - 1).choose j) * 2 ^ j * (-1) ^ n) +
  --   ∑ k ∈ range n, ↑((3 * n + k).choose k) * 2 ^ (3 * n + 1) * (-1) ^ k = 1
  have h_sum1 : (∑ j ∈ range (3 * n + 1), ↑((n + j - 1).choose j) * (2:ℤ) ^ j * (-1) ^ n) = a_z n * (-1) ^ n := by
    unfold a_z
    rw [sum_mul]
  rw [h_sum1] at h
  have h_sum2 : (∑ k ∈ range n, ↑((3 * n + k).choose k) * (2:ℤ) ^ (3 * n + 1) * (-1) ^ k) = 2 ^ (3 * n + 1) * S n := by
    unfold S
    have hd: (∑ k ∈ range n, ↑((3 * n + k).choose k) * (2:ℤ) ^ (3 * n + 1) * (-1) ^ k) = ∑ k ∈ range n, (2:ℤ) ^ (3 * n + 1) * (↑((3 * n + k).choose k) * (-1:ℤ) ^ k) := by
      apply sum_congr rfl
      intro x _
      ring
    rw [hd, ← mul_sum]
  rw [h_sum2] at h
  have h_mul : a_z n * (-1) ^ n * (-1) ^ n = a_z n := by
    have h_pow : (-1 : ℤ) ^ n * (-1) ^ n = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      a_z n * (-1) ^ n * (-1) ^ n = a_z n * ((-1) ^ n * (-1) ^ n) := by ring
      _ = a_z n * 1 := by rw [h_pow]
      _ = a_z n := by ring
  calc
    a_z n = a_z n * (-1) ^ n * (-1) ^ n := h_mul.symm
    _ = (1 - 2 ^ (3 * n + 1) * S n) * (-1) ^ n := by
      have h_eq : a_z n * (-1) ^ n = 1 - 2 ^ (3 * n + 1) * S n := by linarith
      rw [h_eq]
    _ = (-1) ^ n * (1 - 2 ^ (3 * n + 1) * S n) := by ring


lemma a_eq_a_z (n : ℕ) : (a n : ℤ) = a_z n := by
  unfold a a_z
  push_cast
  rfl
