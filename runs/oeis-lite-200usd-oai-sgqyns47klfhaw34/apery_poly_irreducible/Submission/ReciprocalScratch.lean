import FormalConjectures.Util.ProblemImports
open Nat Polynomial

noncomputable def apery_poly_int (n : ℕ) : ℤ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℤ) * (X : ℤ[X]) ^ k

noncomputable def apery_recip_int (n : ℕ) : ℤ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (j : ℕ) ↦
    C (((n.choose j) ^ 2 * ((2 * n - j).choose (n - j)) : ℕ) : ℤ) * (X : ℤ[X]) ^ j

lemma apery_recip_coeff (n j : ℕ) :
    (apery_recip_int n).coeff j = (((n.choose j) ^ 2 * ((2 * n - j).choose (n - j)) : ℕ) : ℤ) := by
  by_cases hj : j ≤ n
  · rw [apery_recip_int, finset_sum_coeff]
    rw [Finset.sum_eq_single j]
    · rw [coeff_C_mul_X_pow]; simp
    · intro b hb hbne
      rw [coeff_C_mul_X_pow]
      rw [if_neg (by intro h; exact hbne h.symm)]
    · intro hnot
      exact False.elim (hnot (by simp only [Finset.mem_range]; exact Nat.lt_succ_of_le hj))
  · have hnj : n < j := Nat.lt_of_not_ge hj
    rw [apery_recip_int, finset_sum_coeff]
    trans 0
    · apply Finset.sum_eq_zero
      intro b hb
      rw [coeff_C_mul_X_pow]
      rw [if_neg]
      intro h
      subst h
      simp only [Finset.mem_range] at hb
      omega
    · simp [Nat.choose_eq_zero_of_lt hnj]

lemma apery_recip_natDegree_le (n : ℕ) : (apery_recip_int n).natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [apery_recip_coeff]
  simp [Nat.choose_eq_zero_of_lt hj]

lemma apery_recip_coeff_top (n : ℕ) : (apery_recip_int n).coeff n = 1 := by
  rw [apery_recip_coeff]
  have hsub1 : 2 * n - n = n := by omega
  have hsub2 : n - n = 0 := by omega
  simp [hsub1, hsub2]

lemma apery_recip_natDegree (n : ℕ) : (apery_recip_int n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact apery_recip_natDegree_le n
  · rw [apery_recip_coeff_top]
    simp

lemma apery_recip_monic (n : ℕ) : (apery_recip_int n).Monic := by
  rw [Monic, leadingCoeff, apery_recip_natDegree, apery_recip_coeff_top]

lemma apery_recip_coeff_zero (n : ℕ) :
    (apery_recip_int n).coeff 0 = (((2 * n).choose n : ℕ) : ℤ) := by
  rw [apery_recip_coeff]
  simp
