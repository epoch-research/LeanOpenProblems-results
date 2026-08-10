import FormalConjectures.Util.ProblemImports

open Finset Nat Polynomial
open scoped BigOperators

lemma choose_pfaff_coeff (n m : ℕ) :
    (∑ k ∈ range (m + 1), n.choose k * n.choose k * (n - k).choose (m - k)) =
      n.choose m * (n + m).choose n := by
  by_cases hmn : m ≤ n
  · calc
      (∑ k ∈ range (m + 1), n.choose k * n.choose k * (n - k).choose (m - k))
          = ∑ k ∈ range (m + 1), n.choose k * (n.choose m * m.choose k) := by
            apply sum_congr rfl
            intro k hk
            have hk_le_m : k ≤ m := by exact Nat.le_of_lt_succ (mem_range.mp hk)
            have hkm : k ≤ m := hk_le_m
            have h := Nat.choose_mul (n := n) (k := m) (s := k) hkm
            -- h: n.choose m * m.choose k = n.choose k * (n-k).choose (m-k)
            rw [h]
            ring
      _ = n.choose m * (∑ k ∈ range (m + 1), n.choose k * m.choose k) := by
            rw [mul_sum]
            apply sum_congr rfl
            intro k hk; ring
      _ = n.choose m * (∑ k ∈ range (m + 1), n.choose k * m.choose (m - k)) := by
            congr 1
            apply sum_congr rfl
            intro k hk
            have hk_le_m : k ≤ m := Nat.le_of_lt_succ (mem_range.mp hk)
            rw [Nat.choose_symm hk_le_m]
      _ = n.choose m * (∑ ij ∈ antidiagonal m, n.choose ij.1 * m.choose ij.2) := by
            congr 1
            rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => n.choose a * m.choose b) m]
      _ = n.choose m * (n + m).choose m := by
            rw [← Nat.add_choose_eq]
      _ = n.choose m * (n + m).choose n := by
            rw [show (n + m).choose m = (n + m).choose n by
              exact Nat.choose_symm_of_eq_add (show n + m = m + n by omega)]
  · have hlt : n < m := Nat.lt_of_not_ge hmn
    calc
      (∑ k ∈ range (m + 1), n.choose k * n.choose k * (n - k).choose (m - k)) = 0 := by
        apply sum_eq_zero
        intro k hk
        have hk_le_m : k ≤ m := Nat.le_of_lt_succ (mem_range.mp hk)
        by_cases hkn : k ≤ n
        · have hmknk : n - k < m - k := by omega
          rw [Nat.choose_eq_zero_of_lt hmknk]
          simp
        · have hnk : n < k := Nat.lt_of_not_ge hkn
          rw [Nat.choose_eq_zero_of_lt hnk]
          simp
      _ = n.choose m * (n + m).choose n := by
        rw [Nat.choose_eq_zero_of_lt hlt]
        simp

#check choose_pfaff_coeff

lemma one_sub_X_eq_neg_X_add_C_neg_one :
    (1 - (X : ℤ[X])) = - (X + C (-1 : ℤ)) := by
  ext k
  by_cases h0 : k = 0
  · subst k; simp
  · by_cases h1 : k = 1
    · subst k; simp; ring
    · simp [coeff_sub, Polynomial.coeff_X]; ring

lemma coeff_one_sub_X_pow_int (n m : ℕ) :
    ((1 - (X : ℤ[X])) ^ n).coeff m = (-1 : ℤ)^m * (n.choose m : ℤ) := by
  rw [one_sub_X_eq_neg_X_add_C_neg_one, neg_pow]
  rw [show ((-1 : ℤ[X]) ^ n) = C ((-1 : ℤ)^n) by simp]
  rw [coeff_C_mul, coeff_X_add_C_pow]
  by_cases hm : m ≤ n
  · have h : n + (n - m) = m + 2 * (n - m) := by omega
    rw [← mul_assoc, ← pow_add, h, pow_add]
    norm_num
  · have hlt : n < m := Nat.lt_of_not_ge hm
    rw [Nat.choose_eq_zero_of_lt hlt]
    simp

#check coeff_one_sub_X_pow_int



lemma coeff_neg_X_pow_mul_one_sub_X_pow (k n m : ℕ) :
    (((- (X : ℤ[X])) ^ k * (1 - (X : ℤ[X])) ^ n).coeff m) =
      if k ≤ m then (-1 : ℤ)^m * (n.choose (m - k) : ℤ) else 0 := by
  rw [neg_pow]
  rw [show ((-1 : ℤ[X]) ^ k) = C ((-1 : ℤ)^k) by simp]
  rw [mul_assoc]
  rw [coeff_C_mul]
  rw [coeff_X_pow_mul']
  by_cases hkm : k ≤ m
  · rw [if_pos hkm, coeff_one_sub_X_pow_int]
    rw [← mul_assoc, ← pow_add]
    have h : k + (m - k) = m := by omega
    rw [h]
    rw [if_pos hkm]

  · rw [if_neg hkm]
    simp [hkm]

#check coeff_neg_X_pow_mul_one_sub_X_pow

lemma shiftedLegendre_pfaff (n : ℕ) :
    (shiftedLegendre n : ℤ[X]) =
      ∑ k ∈ range (n + 1), C ((n.choose k : ℤ) * (n.choose k : ℤ)) *
        (-(X : ℤ[X])) ^ k * (1 - (X : ℤ[X])) ^ (n - k) := by
  ext m
  show (shiftedLegendre n).coeff m =
    (∑ x ∈ range (n + 1), C ((n.choose x : ℤ) * (n.choose x : ℤ)) *
      (-(X : ℤ[X])) ^ x * (1 - (X : ℤ[X])) ^ (n - x)).coeff m
  calc
    (shiftedLegendre n).coeff m
        = (-1 : ℤ)^m * ((n.choose m : ℤ) * ((n + m).choose n : ℤ)) := by
            rw [coeff_shiftedLegendre]
            ring
    _ = (-1 : ℤ)^m *
          (∑ x ∈ range (m + 1),
            (n.choose x : ℤ) * (n.choose x : ℤ) * ((n - x).choose (m - x) : ℤ)) := by
            have hnat := congrArg (fun t : ℕ => (t : ℤ)) (choose_pfaff_coeff n m)
            simp only [Nat.cast_sum, Nat.cast_mul] at hnat
            rw [← hnat]
    _ = (∑ x ∈ range (m + 1),
          (n.choose x : ℤ) * (n.choose x : ℤ) *
            (((-X : ℤ[X]) ^ x * (1 - X) ^ (n - x)).coeff m)) := by
            rw [mul_sum]
            apply sum_congr rfl
            intro x hx
            have hxm : x ≤ m := Nat.le_of_lt_succ (mem_range.mp hx)
            rw [coeff_neg_X_pow_mul_one_sub_X_pow, if_pos hxm]
            ring
    _ = (∑ x ∈ range (n + 1),
          (n.choose x : ℤ) * (n.choose x : ℤ) *
            (((-X : ℤ[X]) ^ x * (1 - X) ^ (n - x)).coeff m)) := by
            by_cases hmn : m ≤ n
            · apply sum_subset (by
                intro x hx
                have hxlt : x < m + 1 := mem_range.mp hx
                exact mem_range.mpr (by omega)) ?_
              intro x hxn hxm
              simp only [mem_range, not_lt] at hxn hxm
              have hmx : ¬ x ≤ m := by omega
              rw [coeff_neg_X_pow_mul_one_sub_X_pow, if_neg hmx]
              simp
            · apply (sum_subset (by
                intro x hx
                have hnm : n < m := Nat.lt_of_not_ge hmn
                have hxlt : x < n + 1 := mem_range.mp hx
                exact mem_range.mpr (by omega)) ?_).symm
              intro x hxm hxn
              simp only [mem_range, not_lt] at hxm hxn
              have hnx : n < x := by omega
              rw [Nat.choose_eq_zero_of_lt hnx]
              simp
    _ = (∑ x ∈ range (n + 1),
          (C ((n.choose x : ℤ) * (n.choose x : ℤ)) *
            (-X : ℤ[X]) ^ x * (1 - X) ^ (n - x)).coeff m) := by
            apply sum_congr rfl
            intro x hx
            symm
            rw [mul_assoc, coeff_C_mul]
    _ = (∑ x ∈ range (n + 1), C ((n.choose x : ℤ) * (n.choose x : ℤ)) *
          (-X : ℤ[X]) ^ x * (1 - X) ^ (n - x)).coeff m := by
            exact (finset_sum_coeff (range (n + 1))
              (fun x => C ((n.choose x : ℤ) * (n.choose x : ℤ)) *
                (-X : ℤ[X]) ^ x * (1 - X) ^ (n - x)) m).symm
  rfl



