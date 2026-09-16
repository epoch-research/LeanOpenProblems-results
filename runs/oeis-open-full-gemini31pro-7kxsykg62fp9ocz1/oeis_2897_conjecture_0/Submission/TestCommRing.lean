import FormalConjectures.Util.ProblemImports
open Finset Nat Polynomial

lemma comm_ring_id {R : Type*} [CommRing R] (A B C : R) (n : ℕ) :
  (A + B) ^ (2 * n) * (A + C) ^ n * (A - C) ^ n =
  ∑ i ∈ range (2 * n + 1), ∑ j ∈ range (n + 1),
    ( ( (2 * n).choose i : R) * (n.choose j : R) * (-1 : R) ^ j ) *
    ( A ^ (4 * n - i - 2 * j) * B ^ i * C ^ (2 * j) ) := by
  have h1 : (A + C) ^ n * (A - C) ^ n = (A ^ 2 - C ^ 2) ^ n := by
    calc (A + C) ^ n * (A - C) ^ n = ((A + C) * (A - C)) ^ n := (mul_pow (A + C) (A - C) n).symm
      _ = (A ^ 2 - C ^ 2) ^ n := by ring_nf
  have h2 : (A ^ 2 - C ^ 2) ^ n = ∑ j ∈ range (n + 1), (- C ^ 2) ^ j * (A ^ 2) ^ (n - j) * (n.choose j : R) := by
    have h_sub : A^2 - C^2 = -C^2 + A^2 := by ring
    rw [h_sub]
    exact add_pow (-C^2) (A^2) n
  have h3 : (A + B) ^ (2 * n) = ∑ i ∈ range (2 * n + 1), B ^ i * A ^ (2 * n - i) * ((2 * n).choose i : R) := by
    have h_sub : A + B = B + A := by ring
    rw [h_sub]
    exact add_pow B A (2 * n)
  calc (A + B) ^ (2 * n) * (A + C) ^ n * (A - C) ^ n
    _ = (A + B) ^ (2 * n) * ((A + C) ^ n * (A - C) ^ n) := by ring
    _ = (∑ i ∈ range (2 * n + 1), B ^ i * A ^ (2 * n - i) * ((2 * n).choose i : R)) *
        (∑ j ∈ range (n + 1), (- C ^ 2) ^ j * (A ^ 2) ^ (n - j) * (n.choose j : R)) := by rw [h1, h3, h2]
    _ = ∑ i ∈ range (2 * n + 1), ∑ j ∈ range (n + 1),
          (B ^ i * A ^ (2 * n - i) * ((2 * n).choose i : R)) *
          ((- C ^ 2) ^ j * (A ^ 2) ^ (n - j) * (n.choose j : R)) := by
      rw [sum_mul]
      apply sum_congr rfl
      intro i hi
      rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  have mem_i : i ≤ 2 * n := by
    have h_lt := mem_range.1 hi
    omega
  have mem_j : j ≤ n := by
    have h_lt := mem_range.1 hj
    omega
  have h_pow1 : (- C ^ 2) ^ j = (-1 : R) ^ j * C ^ (2 * j) := by
    calc (- C ^ 2) ^ j = (-1 * C ^ 2) ^ j := by ring_nf
      _ = (-1 : R) ^ j * (C ^ 2) ^ j := mul_pow (-1 : R) (C ^ 2) j
      _ = (-1 : R) ^ j * C ^ (2 * j) := by rw [pow_mul]
  have h_pow2 : (A ^ 2) ^ (n - j) = A ^ (2 * n - 2 * j) := by
    rw [← pow_mul]
    have h_mul : 2 * (n - j) = 2 * n - 2 * j := by omega
    rw [h_mul]
  have h_pow3 : A ^ (2 * n - i) * A ^ (2 * n - 2 * j) = A ^ (4 * n - i - 2 * j) := by
    rw [← pow_add]
    have h_add : 2 * n - i + (2 * n - 2 * j) = 4 * n - i - 2 * j := by omega
    rw [h_add]
  rw [h_pow1, h_pow2]
  calc (B ^ i * A ^ (2 * n - i) * ↑((2 * n).choose i)) *
      ((-1) ^ j * C ^ (2 * j) * A ^ (2 * n - 2 * j) * ↑(n.choose j))
    _ = (↑((2 * n).choose i) * ↑(n.choose j) * (-1) ^ j) *
        (A ^ (2 * n - i) * A ^ (2 * n - 2 * j) * B ^ i * C ^ (2 * j)) := by ring
    _ = (↑((2 * n).choose i) * ↑(n.choose j) * (-1) ^ j) *
        (A ^ (4 * n - i - 2 * j) * B ^ i * C ^ (2 * j)) := by rw [h_pow3]


