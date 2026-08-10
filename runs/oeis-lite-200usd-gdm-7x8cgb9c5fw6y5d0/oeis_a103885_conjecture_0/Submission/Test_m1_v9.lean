import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

noncomputable def P : Polynomial ℝ := 5 * X^2 - 5 * X + 1

lemma coeff_P_above (N : ℕ) (hN : 2 < N) : P.coeff N = 0 := by
  unfold P
  simp [coeff_add, coeff_sub, coeff_X_pow, coeff_X, coeff_one]
  have h1 : N ≠ 2 := by omega
  have h4 : 1 ≠ N := by omega
  have h5 : N ≠ 0 := by omega
  simp [h1, h4, h5]

lemma coeff_P_two : P.coeff 2 = 5 := by
  unfold P
  simp [coeff_add, coeff_sub, coeff_X_pow, coeff_X, coeff_one]

lemma natDegree_P : P.natDegree = 2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    exact coeff_P_above N hN
  · rw [coeff_P_two]
    norm_num

lemma degree_P : P.degree = (2 : ℕ) := by
  have hP : P ≠ 0 := by
    intro h
    have h_coeff : P.coeff 2 = 0 := by rw [h, coeff_zero]
    rw [coeff_P_two] at h_coeff
    norm_num at h_coeff
  rw [degree_eq_iff_natDegree_eq hP]
  exact natDegree_P
