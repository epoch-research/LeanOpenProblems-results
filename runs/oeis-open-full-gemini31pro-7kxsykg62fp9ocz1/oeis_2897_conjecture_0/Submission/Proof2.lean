import Submission.Proof3

open Finset Nat MvPolynomial


lemma my_small_sum2_eq_coeff_full (n : ℕ) :
  my_small_sum2 n = coeff (xyz_pow_n_local n) (P_n_local n) := by
  unfold my_small_sum2
  rw [coeff_P_n]
  have h_swap : ∑ i ∈ range (2 * n + 1), ∑ j ∈ range (n + 1), ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1),
                  ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
                  ( ((4 * n - i - 2 * j).choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
                  (if n = k ∧ n = u + v ∧ n = i - u + (2 * j - v) then (1 : ℤ) else 0) =
                ∑ j ∈ range (n + 1), ∑ v ∈ range (2 * j + 1), ∑ i ∈ range (2 * n + 1), ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1),
                  ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
                  ( ((4 * n - i - 2 * j).choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
                  (if n = k ∧ n = u + v ∧ n = i - u + (2 * j - v) then (1 : ℤ) else 0) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    exact sum_perm n j _
  rw [h_swap]
  apply sum_congr rfl
  intro j hj
  rw [sum_filter_eq_sum_ite]
  apply sum_congr rfl
  intro v hv
  have hv_le : v ≤ 2 * j := by
    have h1 := mem_range.1 hv
    omega
  have hj_le : j ≤ n := by
    have h1 := mem_range.1 hj
    omega
  have h_inner : ∀ i k u, ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
                  ( ((4 * n - i - 2 * j).choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
                  (if n = k ∧ n = u + v ∧ n = i - u + (2 * j - v) then (1 : ℤ) else 0) =
                  ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
                  ( ((4 * n - i - 2 * j).choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
                  (if k = n then (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) else 0) := by
    intro i k u
    by_cases hu : u ≤ i
    · rw [if_cascade n i j k u v hv_le hu hj_le]
    · have h_zero : (i.choose u : ℤ) = 0 := by
        have h_lt : i < u := by omega
        exact_mod_cast choose_eq_zero_of_lt h_lt
      rw [h_zero]
      simp
  have hc : ∑ i ∈ range (2 * n + 1), ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1),
              (((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j) *
              ( ((4 * n - i - 2 * j).choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
              (if n = k ∧ n = u + v ∧ n = i - u + (2 * j - v) then (1 : ℤ) else 0) =
            ∑ i ∈ range (2 * n + 1), ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1),
              (((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j) *
              ( ((4 * n - i - 2 * j).choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
              (if k = n then (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) else 0) := by
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro u _
    rw [h_inner]
  rw [hc]
  have hc2 : ∑ i ∈ range (2 * n + 1), ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1),
              (((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j) *
              ( ((4 * n - i - 2 * j).choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
              (if k = n then (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) else 0) =
            if v ≤ n then (((2 * n).choose (2 * n - 2 * j) : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j) * ((4 * n - (2 * n - 2 * j) - 2 * j).choose n : ℤ) * ((2 * n - 2 * j).choose (n - v) : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) else 0 := by
    exact collapse_sums n j v
  rw [hc2]
  by_cases hvn : v ≤ n
  · rw [if_pos hvn, if_pos hvn]
    have h_choose : (4 * n - (2 * n - 2 * j) - 2 * j).choose n = (2 * n).choose n := by
      congr 1
      omega
    rw [h_choose]
    have h_choose_symm : (2 * n).choose (2 * n - 2 * j) = (2 * n).choose (2 * j) := by
      have hle : 2 * j ≤ 2 * n := by omega
      exact choose_symm hle
    rw [h_choose_symm]
    have h_neg : (-1 : ℤ) ^ (2 * j - v) = (-1 : ℤ) ^ v := by
      have h1 : (2 * j - v) + v = 2 * j := by omega
      have h2 : (-1 : ℤ) ^ (2 * j - v) * (-1 : ℤ) ^ v = (-1 : ℤ) ^ (2 * j) := by rw [← pow_add, h1]
      have h3 : (-1 : ℤ) ^ (2 * j) = 1 := by
        have h_mul : 2 * j = 2 * j := rfl
        rw [h_mul]
        have hpow : (-1 : ℤ) ^ (2 * j) = ((-1 : ℤ) ^ 2) ^ j := by exact pow_mul (-1) 2 j
        rw [hpow]
        simp
      rw [h3] at h2
      calc (-1 : ℤ) ^ (2 * j - v) = (-1 : ℤ) ^ (2 * j - v) * 1 := by ring
        _ = (-1 : ℤ) ^ (2 * j - v) * ((-1 : ℤ) ^ v * (-1 : ℤ) ^ v) := by
          have hv2 : (-1 : ℤ) ^ v * (-1 : ℤ) ^ v = (1 : ℤ) := by
            rw [← pow_add]
            have h4 : v + v = 2 * v := by omega
            have hpow2 : (-1 : ℤ) ^ (v + v) = ((-1 : ℤ) ^ 2) ^ v := by
              rw [h4]
              exact pow_mul (-1) 2 v
            rw [hpow2]
            simp
          rw [hv2]
        _ = ((-1 : ℤ) ^ (2 * j - v) * (-1 : ℤ) ^ v) * (-1 : ℤ) ^ v := by ring
        _ = 1 * (-1 : ℤ) ^ v := by rw [h2]
        _ = (-1 : ℤ) ^ v := by ring
    rw [h_neg]
    ring
  · rw [if_neg hvn, if_neg hvn]

