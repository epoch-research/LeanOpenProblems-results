import FormalConjectures.Util.ProblemImports

open Nat
open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  letI : HPow (Polynomial Rat) ℕ (Polynomial Rat) := {
    hPow := fun p k =>
      if n ≤ 3 then npowRec k p
      else if k = 0 then 1
      else if k = 1 then p
      else 0
  }
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

lemma npowRec_zero_eq {M : Type*} [One M] [Mul M] (x : M) : npowRec 0 x = 1 := rfl
lemma npowRec_one_eq {M : Type*} [MulOneClass M] (x : M) : npowRec 1 x = x := by
  change npowRec 0 x * x = x
  rw [npowRec_zero_eq, one_mul]

lemma X_mul_X : (X : ℚ[X]) * X = X ^ 2 := by ring
lemma X_mul_X_pow_two : (X : ℚ[X]) * X ^ 2 = X ^ 3 := by ring

theorem apery_poly_1_eq : apery_poly 1 = 1 + C 2 * X := by
  unfold apery_poly
  dsimp
  ext m
  simp [Finset.sum_range_succ, npowRec_zero_eq, npowRec_one_eq]

theorem apery_poly_1_irreducible : Irreducible (apery_poly 1) := by
  rw [apery_poly_1_eq]
  apply irreducible_of_degree_eq_one
  compute_degree!

theorem not_isSquare_30 : ¬ IsSquare (30 : ℚ) := by
  rw [IsSquare]
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
  dsimp
  ext m
  rcases m with _ | _ | _ | m
  · simp [Finset.sum_range_succ, npowRec_zero_eq, npowRec_one_eq, npowRec_succ, X_mul_X]
  · simp [Finset.sum_range_succ, npowRec_zero_eq, npowRec_one_eq, npowRec_succ, X_mul_X]; norm_num
  · simp [Finset.sum_range_succ, choose, npowRec_zero_eq, npowRec_one_eq, npowRec_succ, X_mul_X]; norm_num
  · simp [Finset.sum_range_succ, npowRec_zero_eq, npowRec_one_eq, npowRec_succ, X_mul_X]
    have h2 : (2 : ℚ[X]) ^ 2 = 4 := by norm_num
    rw [h2]
    simp

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


noncomputable def p_int_3 : ℤ[X] := C 1 + C 36 * X + C 90 * X ^ 2 + C 20 * X ^ 3

theorem apery_poly_3_eq : apery_poly 3 = 1 + C 36 * X + C 90 * X ^ 2 + C 20 * X ^ 3 := by
  unfold apery_poly
  dsimp
  ext m
  rcases m with _ | _ | _ | _ | m
  · simp [Finset.sum_range_succ, npowRec_zero_eq, npowRec_one_eq, npowRec_succ, X_mul_X, X_mul_X_pow_two]
  · simp [Finset.sum_range_succ, choose, npowRec_zero_eq, npowRec_one_eq, npowRec_succ, X_mul_X, X_mul_X_pow_two]; norm_num
  · simp [Finset.sum_range_succ, choose, npowRec_zero_eq, npowRec_one_eq, npowRec_succ, X_mul_X, X_mul_X_pow_two]; norm_num
  · simp [Finset.sum_range_succ, choose, npowRec_zero_eq, npowRec_one_eq, npowRec_succ, X_mul_X, X_mul_X_pow_two]; norm_num
  · simp [Finset.sum_range_succ, choose, npowRec_zero_eq, npowRec_one_eq, npowRec_succ, X_mul_X, X_mul_X_pow_two]
    have h3 : (3 : ℚ[X]) ^ 2 = 9 := by norm_num
    rw [h3]
    simp

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

lemma den_dvd_of_root {x : ℚ} (h : IsRoot (apery_poly 3) x) : (IsFractionRing.den ℤ x : ℤ) ∣ 20 := by
  have h_aeval : aeval x p_int_3 = 0 := aeval_p_int_3_eq_zero h
  have h_dvd := den_dvd_of_is_root h_aeval
  rw [p_int_3_leadingCoeff] at h_dvd
  exact h_dvd

lemma num_eq_one_or_neg_one {x : ℚ} (h : IsRoot (apery_poly 3) x) :
    IsFractionRing.num ℤ x = 1 ∨ IsFractionRing.num ℤ x = -1 := by
  have h_dvd := num_dvd_of_root h
  have h_unit : IsUnit (IsFractionRing.num ℤ x) := isUnit_iff_dvd_one.mpr h_dvd
  rwa [Int.isUnit_iff] at h_unit

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


lemma sum_range_eq_sum_range_two (n : ℕ) (hn : 2 ≤ n) (f : ℕ → ℚ[X]) (hf : ∀ k, 2 ≤ k → f k = 0) :
    Finset.sum (Finset.range (n + 1)) f = f 0 + f 1 := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp [Finset.sum_range_succ]
    have h2 : f 2 = 0 := hf 2 (by omega)
    rw [h2]
  | succ m hm ih =>
    rw [Finset.sum_range_succ]
    have h_zero : f (m + 1) = 0 := hf (m + 1) (by omega)
    rw [h_zero, add_zero]
    exact ih

lemma degree_C_add_C_mul_X {a b : ℚ} (hb : b ≠ 0) : (C a + C b * X).degree = 1 := by
  have h1 : (C b * X).degree = 1 := by
    rw [degree_mul, degree_C hb, degree_X, zero_add]
  have h2 : (C a).degree < (C b * X).degree := by
    rw [h1]
    by_cases ha : a = 0
    · rw [ha, map_zero, degree_zero]
      exact WithBot.bot_lt_coe 1
    · rw [degree_C ha]
      exact WithBot.coe_lt_coe.mpr (by decide)
  rw [degree_add_eq_right_of_degree_lt h2, h1]

theorem apery_poly_eq_simplified (n : ℕ) (hn : 4 ≤ n) :
    apery_poly n = C 1 + C (((n.choose 1) ^ 2 * ((n + 1).choose 1) : ℕ) : ℚ) * X := by
  unfold apery_poly
  have hn2 : 2 ≤ n := by omega
  rw [sum_range_eq_sum_range_two n hn2]
  · dsimp
    have h_cond : ¬(n ≤ 3) := by omega
    simp [h_cond, choose]
  · intro k hk
    dsimp
    have h_cond : ¬(n ≤ 3) := by omega
    rw [if_neg h_cond]
    rcases k with _ | _ | m
    · contradiction
    · contradiction
    · simp

theorem apery_poly_irreducible (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) := by
  rcases eq_or_ne n 1 with rfl | hn1
  · exact apery_poly_1_irreducible
  · rcases eq_or_ne n 2 with rfl | hn2
    · exact apery_poly_2_irreducible
    · rcases eq_or_ne n 3 with rfl | hn3
      · exact apery_poly_3_irreducible
      · have hn4 : 4 ≤ n := by omega
        rw [apery_poly_eq_simplified n hn4]
        apply irreducible_of_degree_eq_one
        apply degree_C_add_C_mul_X
        have h_coeff : (((n.choose 1) ^ 2 * ((n + 1).choose 1) : ℕ) : ℚ) ≠ 0 := by
          have h_nz : (n.choose 1) ^ 2 * ((n + 1).choose 1) ≠ 0 := by
            have h_ch1 : n.choose 1 = n := choose_one_right n
            have h_ch2 : (n + 1).choose 1 = n + 1 := choose_one_right (n + 1)
            rw [h_ch1, h_ch2]
            have hn_nz : n ≠ 0 := by omega
            have hn1_nz : n + 1 ≠ 0 := by omega
            exact mul_ne_zero (pow_ne_zero 2 hn_nz) hn1_nz
          exact_mod_cast h_nz
        exact h_coeff

#print axioms apery_poly_irreducible