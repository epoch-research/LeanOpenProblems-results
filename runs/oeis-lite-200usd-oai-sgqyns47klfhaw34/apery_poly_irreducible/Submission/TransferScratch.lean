import FormalConjectures.Util.ProblemImports
open Nat Polynomial

noncomputable def apery_poly_int (n : ℕ) : ℤ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℤ) * (X : ℤ[X]) ^ k

noncomputable def apery_recip_int (n : ℕ) : ℤ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (j : ℕ) ↦
    C (((n.choose j) ^ 2 * ((2 * n - j).choose (n - j)) : ℕ) : ℤ) * (X : ℤ[X]) ^ j

lemma apery_poly_int_coeff (n k : ℕ) :
    (apery_poly_int n).coeff k = (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℤ) := by
  by_cases hk : k < n + 1
  · rw [apery_poly_int, finset_sum_coeff]
    rw [Finset.sum_eq_single k]
    · rw [coeff_C_mul_X_pow]; simp
    · intro b hb hbne; rw [coeff_C_mul_X_pow]; rw [if_neg (by intro h; exact hbne h.symm)]
    · intro hnot; exact False.elim (hnot (by simpa using hk))
  · have hnk : n < k := by omega
    rw [apery_poly_int, finset_sum_coeff]
    trans 0
    · apply Finset.sum_eq_zero
      intro i hi
      rw [coeff_C_mul_X_pow]
      rw [if_neg]
      intro hki; subst hki; exact hk (Finset.mem_range.mp hi)
    · simp [Nat.choose_eq_zero_of_lt hnk]

lemma apery_poly_int_natDegree_le (n : ℕ) : (apery_poly_int n).natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [apery_poly_int_coeff]
  simp [Nat.choose_eq_zero_of_lt hk]

lemma apery_poly_int_coeff_top (n : ℕ) : (apery_poly_int n).coeff n = (((2*n).choose n : ℕ) : ℤ) := by
  rw [apery_poly_int_coeff]
  have h : n + n = 2 * n := by omega
  simp [h]

lemma apery_poly_int_natDegree (n : ℕ) : (apery_poly_int n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact apery_poly_int_natDegree_le n
  · rw [apery_poly_int_coeff_top]
    exact_mod_cast (Nat.choose_pos (by omega : n ≤ 2*n)).ne'

lemma apery_recip_coeff (n j : ℕ) :
    (apery_recip_int n).coeff j = (((n.choose j) ^ 2 * ((2 * n - j).choose (n - j)) : ℕ) : ℤ) := by
  by_cases hj : j < n + 1
  · rw [apery_recip_int, finset_sum_coeff]
    rw [Finset.sum_eq_single j]
    · rw [coeff_C_mul_X_pow]; simp
    · intro b hb hbne; rw [coeff_C_mul_X_pow]; rw [if_neg (by intro h; exact hbne h.symm)]
    · intro hnot; exact False.elim (hnot (by simpa using hj))
  · have hjn : n < j := by omega
    rw [apery_recip_int, finset_sum_coeff]
    trans 0
    · apply Finset.sum_eq_zero
      intro i hi
      rw [coeff_C_mul_X_pow]
      rw [if_neg]
      intro hji; subst hji; exact hj (Finset.mem_range.mp hi)
    · simp [Nat.choose_eq_zero_of_lt hjn]

lemma apery_recip_natDegree_le (n : ℕ) : (apery_recip_int n).natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [apery_recip_coeff]
  simp [Nat.choose_eq_zero_of_lt hk]

lemma apery_recip_coeff_top (n : ℕ) : (apery_recip_int n).coeff n = 1 := by
  rw [apery_recip_coeff]
  simp

lemma apery_recip_natDegree (n : ℕ) : (apery_recip_int n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact apery_recip_natDegree_le n
  · rw [apery_recip_coeff_top]
    norm_num

lemma apery_recip_monic (n : ℕ) : (apery_recip_int n).Monic := by
  rw [Monic, leadingCoeff, apery_recip_natDegree, apery_recip_coeff_top]

lemma reverse_apery_poly_int (n : ℕ) : (apery_poly_int n).reverse = apery_recip_int n := by
  ext j
  rw [coeff_reverse, apery_poly_int_natDegree]
  by_cases hj : j ≤ n
  · have hrev : (revAt n) j = n - j := by simp [revAt, hj]
    rw [hrev, apery_recip_coeff, apery_poly_int_coeff]
    have h1 : n.choose (n - j) = n.choose j := Nat.choose_symm hj
    have h2 : n + (n - j) = 2 * n - j := by omega
    rw [h1, h2]
  · have hlt : n < j := by omega
    have hrev : (revAt n) j = j := by simp [revAt, hj]
    rw [hrev, apery_recip_coeff, apery_poly_int_coeff]
    simp [Nat.choose_eq_zero_of_lt hlt]
