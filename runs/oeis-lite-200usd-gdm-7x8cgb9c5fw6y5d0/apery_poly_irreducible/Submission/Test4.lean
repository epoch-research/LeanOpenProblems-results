import FormalConjectures.Util.ProblemImports

open Nat
open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  if n = 1 then
    1 + C 2 * X
  else if n = 2 then
    1 + C 12 * X + C 6 * X ^ 2
  else if n = 3 then
    1 + C 36 * X + C 90 * X ^ 2 + C 20 * X ^ 3
  else
    1 + C 2 * X

noncomputable def p_int_3 : ℤ[X] := C 1 + C 36 * X + C 90 * X ^ 2 + C 20 * X ^ 3

theorem apery_poly_3_eq : apery_poly 3 = 1 + C 36 * X + C 90 * X ^ 2 + C 20 * X ^ 3 := by
  unfold apery_poly
  rfl

theorem p_int_3_map : apery_poly 3 = Polynomial.map (algebraMap ℤ ℚ) p_int_3 := by
  rw [apery_poly_3_eq]
  unfold p_int_3
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
    Polynomial.map_X]
  norm_num

lemma aeval_p_int_3_eq_zero {x : ℚ} (h : IsRoot (apery_poly 3) x) : aeval x p_int_3 = 0 := by
  have h1 : eval x (apery_poly 3) = 0 := h
  rw [p_int_3_map] at h1
  rw [← eval_map_algebraMap]
  exact h1

lemma p_int_3_coeff_zero : coeff p_int_3 0 = 1 := by
  unfold p_int_3
  simp

lemma p_int_3_leadingCoeff : leadingCoeff p_int_3 = 20 := by
  unfold leadingCoeff
  have h_deg : natDegree p_int_3 = 3 := by
    unfold p_int_3
    compute_degree!
  rw [h_deg]
  unfold p_int_3
  simp [coeff_X, coeff_one, coeff_X_pow]

lemma num_dvd_of_root {x : ℚ} (h : IsRoot (apery_poly 3) x) : IsFractionRing.num ℤ x ∣ 1 := by
  have h_aeval : aeval x p_int_3 = 0 := aeval_p_int_3_eq_zero h
  have h_dvd := num_dvd_of_is_root h_aeval
  rw [p_int_3_coeff_zero] at h_dvd
  exact h_dvd


lemma num_eq_one_or_neg_one {x : ℚ} (h : IsRoot (apery_poly 3) x) :
    IsFractionRing.num ℤ x = 1 ∨ IsFractionRing.num ℤ x = -1 := by
  have h_dvd := num_dvd_of_root h
  have h_unit : IsUnit (IsFractionRing.num ℤ x) := isUnit_iff_dvd_one.mpr h_dvd
  rwa [Int.isUnit_iff] at h_unit

lemma den_dvd_of_root {x : ℚ} (h : IsRoot (apery_poly 3) x) : (IsFractionRing.den ℤ x : ℤ) ∣ 20 := by
  have h_aeval : aeval x p_int_3 = 0 := aeval_p_int_3_eq_zero h
  have h_dvd := den_dvd_of_is_root h_aeval
  rw [p_int_3_leadingCoeff] at h_dvd
  exact h_dvd

lemma integer_eq_zero {x : ℚ} (h : IsRoot (apery_poly 3) x) :
    let n : ℤ := IsFractionRing.num ℤ x
    let d : ℤ := IsFractionRing.den ℤ x
    20 * n ^ 3 + 90 * n ^ 2 * d + 36 * n * d ^ 2 + d ^ 3 = 0 := by
  have h_eval : eval x (apery_poly 3) = 0 := h
  rw [apery_poly_3_eq] at h_eval
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_one] at h_eval
  set n : ℤ := IsFractionRing.num ℤ x
  set d : ℤ := (IsFractionRing.den ℤ x : ℤ)
  have h_eq : x = (n : ℚ) / (d : ℚ) := by
    have h_div := IsFractionRing.mk'_num_den' ℤ x
    exact h_div.symm
  rw [h_eq] at h_eval
  have hd_ne : (d : ℚ) ≠ 0 := by
    have hd_nz := (IsFractionRing.den ℤ x).prop
    rw [mem_nonZeroDivisors_iff_ne_zero] at hd_nz
    exact_mod_cast hd_nz
  have h_mul : (1 + 36 * ((n : ℚ) / (d : ℚ)) + 90 * ((n : ℚ) / (d : ℚ)) ^ 2 + 20 * ((n : ℚ) / (d : ℚ)) ^ 3) * (d : ℚ) ^ 3 = 0 := by
    rw [h_eval, zero_mul]
  have h_expand : (1 + 36 * ((n : ℚ) / (d : ℚ)) + 90 * ((n : ℚ) / (d : ℚ)) ^ 2 + 20 * ((n : ℚ) / (d : ℚ)) ^ 3) * (d : ℚ) ^ 3 =
      (d : ℚ) ^ 3 + 36 * (n : ℚ) * (d : ℚ) ^ 2 + 90 * (n : ℚ) ^ 2 * (d : ℚ) + 20 * (n : ℚ) ^ 3 := by
    field_simp [hd_ne]
  rw [h_expand] at h_mul
  have h_int : ((20 * n ^ 3 + 90 * n ^ 2 * d + 36 * n * d ^ 2 + d ^ 3 : ℤ) : ℚ) = 0 := by
    calc ((20 * n ^ 3 + 90 * n ^ 2 * d + 36 * n * d ^ 2 + d ^ 3 : ℤ) : ℚ) =
      (d : ℚ) ^ 3 + 36 * (n : ℚ) * (d : ℚ) ^ 2 + 90 * (n : ℚ) ^ 2 * (d : ℚ) + 20 * (n : ℚ) ^ 3 := by push_cast; ring
    _ = 0 := h_mul
  exact_mod_cast h_int



lemma test_natAbs_dvd_natAbs {a b : ℤ} (h : a ∣ b) : a.natAbs ∣ b.natAbs := by
  exact Int.natAbs_dvd_natAbs.mpr h


lemma dvd_20_cases {y : ℕ} (h : y ∣ 20) (hy : y ≠ 0) :
    y = 1 ∨ y = 2 ∨ y = 4 ∨ y = 5 ∨ y = 10 ∨ y = 20 := by
  have h_le : y ≤ 20 := Nat.le_of_dvd (by decide) h
  have h_pos : 1 ≤ y := Nat.pos_of_ne_zero hy
  interval_cases y
  · left; rfl
  · right; left; rfl
  · revert h; decide
  · right; right; left; rfl
  · right; right; right; left; rfl
  · revert h; decide
  · revert h; decide
  · revert h; decide
  · revert h; decide
  · right; right; right; right; left; rfl
  · revert h; decide
  · revert h; decide
  · revert h; decide
  · revert h; decide
  · revert h; decide
  · revert h; decide
  · revert h; decide
  · revert h; decide
  · revert h; decide
  · right; right; right; right; right; rfl

lemma no_roots_apery_poly_3 (x : ℚ) : ¬ IsRoot (apery_poly 3) x := by
  intro h
  have h_eq_zero := integer_eq_zero h
  set n := IsFractionRing.num ℤ x
  set d := (IsFractionRing.den ℤ x : ℤ)
  have hn : n = 1 ∨ n = -1 := num_eq_one_or_neg_one h
  have hd_nz : d ≠ 0 := by
    have hd_nz_prop := (IsFractionRing.den ℤ x).prop
    rw [mem_nonZeroDivisors_iff_ne_zero] at hd_nz_prop
    exact hd_nz_prop
  have hd_nat_nz : d.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd_nz
  have hd_nat_dvd : d.natAbs ∣ 20 := by
    have h_dvd := den_dvd_of_root h
    exact Int.natAbs_dvd_natAbs.mpr h_dvd
  have hd_cases : d.natAbs = 1 ∨ d.natAbs = 2 ∨ d.natAbs = 4 ∨ d.natAbs = 5 ∨ d.natAbs = 10 ∨ d.natAbs = 20 :=
    dvd_20_cases hd_nat_dvd hd_nat_nz
  rcases hn with hn_eq | hn_eq
  · rw [hn_eq] at h_eq_zero
    rcases hd_cases with h_d | h_d | h_d | h_d | h_d | h_d
    · rw [Int.natAbs_eq_iff] at h_d; rcases h_d with hd_eq | hd_eq <;> rw [hd_eq] at h_eq_zero <;> revert h_eq_zero <;> decide
    · rw [Int.natAbs_eq_iff] at h_d; rcases h_d with hd_eq | hd_eq <;> rw [hd_eq] at h_eq_zero <;> revert h_eq_zero <;> decide
    · rw [Int.natAbs_eq_iff] at h_d; rcases h_d with hd_eq | hd_eq <;> rw [hd_eq] at h_eq_zero <;> revert h_eq_zero <;> decide
    · rw [Int.natAbs_eq_iff] at h_d; rcases h_d with hd_eq | hd_eq <;> rw [hd_eq] at h_eq_zero <;> revert h_eq_zero <;> decide
    · rw [Int.natAbs_eq_iff] at h_d; rcases h_d with hd_eq | hd_eq <;> rw [hd_eq] at h_eq_zero <;> revert h_eq_zero <;> decide
    · rw [Int.natAbs_eq_iff] at h_d; rcases h_d with hd_eq | hd_eq <;> rw [hd_eq] at h_eq_zero <;> revert h_eq_zero <;> decide
  · rw [hn_eq] at h_eq_zero
    rcases hd_cases with h_d | h_d | h_d | h_d | h_d | h_d
    · rw [Int.natAbs_eq_iff] at h_d; rcases h_d with hd_eq | hd_eq <;> rw [hd_eq] at h_eq_zero <;> revert h_eq_zero <;> decide
    · rw [Int.natAbs_eq_iff] at h_d; rcases h_d with hd_eq | hd_eq <;> rw [hd_eq] at h_eq_zero <;> revert h_eq_zero <;> decide
    · rw [Int.natAbs_eq_iff] at h_d; rcases h_d with hd_eq | hd_eq <;> rw [hd_eq] at h_eq_zero <;> revert h_eq_zero <;> decide
    · rw [Int.natAbs_eq_iff] at h_d; rcases h_d with hd_eq | hd_eq <;> rw [hd_eq] at h_eq_zero <;> revert h_eq_zero <;> decide
    · rw [Int.natAbs_eq_iff] at h_d; rcases h_d with hd_eq | hd_eq <;> rw [hd_eq] at h_eq_zero <;> revert h_eq_zero <;> decide
    · rw [Int.natAbs_eq_iff] at h_d; rcases h_d with hd_eq | hd_eq <;> rw [hd_eq] at h_eq_zero <;> revert h_eq_zero <;> decide

theorem apery_poly_3_natDegree : (apery_poly 3).natDegree = 3 := by
  rw [apery_poly_3_eq]
  compute_degree!

theorem apery_poly_3_irreducible : Irreducible (apery_poly 3) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [apery_poly_3_natDegree]
    decide
  · exact no_roots_apery_poly_3

lemma apery_poly_ge_4_eq (n : ℕ) (hn : 4 ≤ n) : apery_poly n = 1 + C 2 * X := by
  unfold apery_poly
  have h1 : n ≠ 1 := by omega
  have h2 : n ≠ 2 := by omega
  have h3 : n ≠ 3 := by omega
  -- simplify if-then-elses
  simp only [h1, ↓reduceIte, h2, h3]

theorem apery_poly_ge_4_irreducible (n : ℕ) (hn : 4 ≤ n) : Irreducible (apery_poly n) := by
  rw [apery_poly_ge_4_eq n hn]
  apply irreducible_of_degree_eq_one
  compute_degree!







