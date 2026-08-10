import FormalConjectures.Util.ProblemImports

open Nat
open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

theorem apery_poly_1_eq : apery_poly 1 = 1 + C 2 * X := by
  unfold apery_poly
  ext m
  simp [Finset.sum_range_succ]

theorem apery_poly_1_irreducible : Irreducible (apery_poly 1) := by
  rw [apery_poly_1_eq]
  apply irreducible_of_degree_eq_one
  compute_degree!

theorem not_isSquare_30 : ¬ IsSquare (30 : ℚ) := by
  rw [IsSquare]
  -- Since IsSquare is ∃ q, x = q * q, let's rewrite to ∃ q, q * q = x
  have h : (∃ q, (30 : ℚ) = q * q) ↔ (∃ q, q * q = (30 : ℚ)) := by
    simp_rw [eq_comm]
  rw [h]
  rw [Rat.exists_mul_self]
  norm_num

lemma quadratic_eq_zero_iff_30 (x : ℚ) : 6 * x ^ 2 + 12 * x + 1 = 0 ↔ (6 * x + 6) ^ 2 = 30 := by
  constructor
  · intro h
    calc (6 * x + 6) ^ 2 = 36 * x ^ 2 + 72 * x + 36 := by ring
    _ = 6 * (6 * x ^ 2 + 12 * x + 1) + 30 := by ring
    _ = 6 * 0 + 30 := by rw [h]
    _ = 30 := by ring
  · intro h
    have h1 : 6 * (6 * x ^ 2 + 12 * x + 1) = 0 := by
      calc 6 * (6 * x ^ 2 + 12 * x + 1) = (6 * x + 6) ^ 2 - 30 := by ring
      _ = 30 - 30 := by rw [h]
      _ = 0 := by ring
    exact mul_eq_zero.mp h1 |>.resolve_left (by norm_num)

theorem apery_poly_2_eq : apery_poly 2 = 1 + C 12 * X + C 6 * X ^ 2 := by
  unfold apery_poly
  simp [Finset.sum_range_succ, choose, C_eq_algebraMap]
  norm_num

lemma eval_apery_poly_2 (x : ℚ) : eval x (apery_poly 2) = 6 * x ^ 2 + 12 * x + 1 := by
  rw [apery_poly_2_eq]
  simp [eval_add, eval_C, eval_mul, eval_pow, eval_X]
  ring

lemma no_roots_apery_poly_2 (x : ℚ) : ¬ IsRoot (apery_poly 2) x := by
  intro h
  rw [IsRoot, eval_apery_poly_2] at h
  rw [quadratic_eq_zero_iff_30] at h
  have h_sq : IsSquare (30 : ℚ) := by
    use 6 * x + 6
    rw [pow_two] at h
    exact h.symm
  exact not_isSquare_30 h_sq

theorem apery_poly_2_natDegree : (apery_poly 2).natDegree = 2 := by
  rw [apery_poly_2_eq]
  compute_degree!

theorem apery_poly_2_irreducible : Irreducible (apery_poly 2) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [apery_poly_2_natDegree]
    decide
  · exact no_roots_apery_poly_2
