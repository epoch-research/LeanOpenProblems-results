import FormalConjectures.Util.ProblemImports

open Nat Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

lemma apery_coeff_one_ne_zero (n : ℕ) (hn : 1 ≤ n) : (apery_poly n).coeff 1 ≠ 0 := by
  have hcoeff : (apery_poly n).coeff 1 = (((n.choose 1) ^ 2 * ((n + 1).choose 1) : ℕ) : ℚ) := by
    rw [apery_poly, finset_sum_coeff]
    rw [Finset.sum_eq_single 1]
    · rw [coeff_C_mul_X_pow]; simp
    · intro b hb hbne; rw [coeff_C_mul_X_pow]; rw [if_neg (by intro h; exact hbne h.symm)]
    · intro hnot; exact False.elim (hnot (by simp only [Finset.mem_range]; exact Nat.lt_succ_of_le hn))
  rw [hcoeff]
  have hn0 : n ≠ 0 := by exact Nat.ne_of_gt hn
  have hnat : (n.choose 1) ^ 2 * ((n + 1).choose 1) ≠ 0 := by
    simp [Nat.choose_one_right, hn0]
  exact_mod_cast hnat

lemma apery_not_isUnit (n : ℕ) (hn : 1 ≤ n) : ¬ IsUnit (apery_poly n) := by
  intro hu
  have hdeg := Polynomial.degree_eq_zero_of_isUnit hu
  have hcoeff0 : (apery_poly n).coeff 1 = 0 := by
    exact coeff_eq_zero_of_degree_lt (by simpa using hdeg ▸ (by decide : (1:WithBot ℕ) > 0))
  exact apery_coeff_one_ne_zero n hn hcoeff0

lemma apery_coeff_eq_of_le (n k : ℕ) (hk : k ≤ n) :
    (apery_poly n).coeff k = (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) := by
  rw [apery_poly, finset_sum_coeff]
  rw [Finset.sum_eq_single k]
  · rw [coeff_C_mul_X_pow]; simp
  · intro b hb hbne
    rw [coeff_C_mul_X_pow]
    rw [if_neg (by intro h; exact hbne h.symm)]
  · intro hnot
    exact False.elim (hnot (by simp only [Finset.mem_range]; exact Nat.lt_succ_of_le hk))

lemma apery_coeff_eq_zero_of_lt (n k : ℕ) (hk : n < k) : (apery_poly n).coeff k = 0 := by
  rw [apery_poly, finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro b hb
  rw [coeff_C_mul_X_pow]
  rw [if_neg]
  intro h
  subst h
  simp only [Finset.mem_range] at hb
  omega

lemma apery_coeff_natDegree_nonzero (n : ℕ) : (apery_poly n).coeff n ≠ 0 := by
  rw [apery_coeff_eq_of_le n n le_rfl]
  have hchoose : 0 < (n + n).choose n := Nat.choose_pos (by omega)
  have hnat : (n.choose n) ^ 2 * ((n + n).choose n) ≠ 0 := by
    simp [hchoose.ne']
  exact_mod_cast hnat

lemma apery_natDegree (n : ℕ) : (apery_poly n).natDegree = n := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    exact apery_coeff_eq_zero_of_lt n k hk
  · exact apery_coeff_natDegree_nonzero n

lemma apery_ne_zero (n : ℕ) : apery_poly n ≠ 0 := by
  intro h
  have hc := apery_coeff_natDegree_nonzero n
  rw [h] at hc
  simp at hc
