import FormalConjectures.Util.ProblemImports

open Polynomial

noncomputable def p_int : ℤ[X] := 20 * X ^ 3 + 90 * X ^ 2 + 36 * X + 1

lemma p_int_coeff_0 : p_int.coeff 0 = 1 := by
  simp [p_int]

lemma p_int_coeff_3 : p_int.coeff 3 = 20 := by
  simp [p_int, coeff_X, coeff_one]

lemma p_int_natDegree : p_int.natDegree = 3 := by
  dsimp [p_int]
  compute_degree!

lemma p_int_leadingCoeff : p_int.leadingCoeff = 20 := by
  have : p_int.leadingCoeff = p_int.coeff p_int.natDegree := rfl
  rw [this, p_int_natDegree, p_int_coeff_3]

lemma p_int_map : map (Int.castRingHom ℚ) p_int = 20 * X ^ 3 + 90 * X ^ 2 + 36 * X + 1 := by
  dsimp [p_int]
  simp [Int.castRingHom]

lemma aeval_p_int_eq_zero (r : ℚ) (hr : eval r (20 * X ^ 3 + 90 * X ^ 2 + 36 * X + 1) = 0) :
    aeval r p_int = 0 := by
  change eval₂ (algebraMap ℤ ℚ) r p_int = 0
  rw [eval₂_eq_eval_map]
  have h_map : map (algebraMap ℤ ℚ) p_int = map (Int.castRingHom ℚ) p_int := rfl
  rw [h_map, p_int_map, hr]

lemma num_dvd_1 (x : ℚ) (hx : aeval x p_int = 0) : x.num ∣ 1 := by
  have h1 : IsFractionRing.num ℤ x ∣ p_int.coeff 0 := num_dvd_of_is_root hx
  rw [p_int_coeff_0] at h1
  have h2 : x.num ∣ IsFractionRing.num ℤ x := (Rat.isFractionRingNum x).symm.dvd
  exact dvd_trans h2 h1

lemma den_dvd_20 (x : ℚ) (hx : aeval x p_int = 0) : x.den ∣ 20 := by
  have h1 : (IsFractionRing.den ℤ x : ℤ) ∣ p_int.leadingCoeff := den_dvd_of_is_root hx
  rw [p_int_leadingCoeff] at h1
  have h2 : (IsFractionRing.den ℤ x : ℤ).natAbs ∣ (20 : ℤ).natAbs := Int.natAbs_dvd_natAbs.mpr h1
  rw [Rat.isFractionRingDen x] at h2
  exact h2

lemma no_roots_3 (x : ℚ) (hx : eval x (20 * X ^ 3 + 90 * X ^ 2 + 36 * X + 1) = 0) : False := by
  have h_aeval : aeval x p_int = 0 := aeval_p_int_eq_zero x hx
  have h_num : x.num ∣ 1 := num_dvd_1 x h_aeval
  have h_den : x.den ∣ 20 := den_dvd_20 x h_aeval
  have h_num_cases : x.num = 1 ∨ x.num = -1 := by
    have h_unit : IsUnit x.num := isUnit_iff_dvd_one.mpr h_num
    exact Int.isUnit_iff.mp h_unit
  have h_den_pos : x.den > 0 := x.den_pos
  have h_den_le : x.den ≤ 20 := Nat.le_of_dvd (by decide) h_den
  generalize h_den_eq : x.den = d at h_den h_den_pos h_den_le
  rcases h_num_cases with h_num_eq | h_num_eq
  · interval_cases d
    · have h_x : x = 1 := by
        rw [← Rat.num_div_den x, h_num_eq, h_den_eq]
        norm_num
      rw [h_x] at hx
      revert hx
      norm_num
    · have h_x : x = 1 / 2 := by
        rw [← Rat.num_div_den x, h_num_eq, h_den_eq]
        norm_num
      rw [h_x] at hx
      revert hx
      norm_num
    · revert h_den; decide
    · have h_x : x = 1 / 4 := by
        rw [← Rat.num_div_den x, h_num_eq, h_den_eq]
        norm_num
      rw [h_x] at hx
      revert hx
      norm_num
    · have h_x : x = 1 / 5 := by
        rw [← Rat.num_div_den x, h_num_eq, h_den_eq]
        norm_num
      rw [h_x] at hx
      revert hx
      norm_num
    · revert h_den; decide
    · revert h_den; decide
    · revert h_den; decide
    · revert h_den; decide
    · have h_x : x = 1 / 10 := by
        rw [← Rat.num_div_den x, h_num_eq, h_den_eq]
        norm_num
      rw [h_x] at hx
      revert hx
      norm_num
    · revert h_den; decide
    · revert h_den; decide
    · revert h_den; decide
    · revert h_den; decide
    · revert h_den; decide
    · revert h_den; decide
    · revert h_den; decide
    · revert h_den; decide
    · revert h_den; decide
    · have h_x : x = 1 / 20 := by
        rw [← Rat.num_div_den x, h_num_eq, h_den_eq]
        norm_num
      rw [h_x] at hx
      revert hx
      norm_num
  · interval_cases d
    · have h_x : x = -1 := by
        rw [← Rat.num_div_den x, h_num_eq, h_den_eq]
        norm_num
      rw [h_x] at hx
      revert hx
      norm_num
    · have h_x : x = -1 / 2 := by
        rw [← Rat.num_div_den x, h_num_eq, h_den_eq]
        norm_num
      rw [h_x] at hx
      revert hx
      norm_num
    · revert h_den; decide
    · have h_x : x = -1 / 4 := by
        rw [← Rat.num_div_den x, h_num_eq, h_den_eq]
        norm_num
      rw [h_x] at hx
      revert hx
      norm_num
    · have h_x : x = -1 / 5 := by
        rw [← Rat.num_div_den x, h_num_eq, h_den_eq]
        norm_num
      rw [h_x] at hx
      revert hx
      norm_num
    · revert h_den; decide
    · revert h_den; decide
    · revert h_den; decide
    · revert h_den; decide
    · have h_x : x = -1 / 10 := by
        rw [← Rat.num_div_den x, h_num_eq, h_den_eq]
        norm_num
      rw [h_x] at hx
      revert hx
      norm_num
    · revert h_den; decide
    · revert h_den; decide
    · revert h_den; decide
    · revert h_den; decide
    · revert h_den; decide
    · revert h_den; decide
    · revert h_den; decide
    · revert h_den; decide
    · revert h_den; decide
    · have h_x : x = -1 / 20 := by
        rw [← Rat.num_div_den x, h_num_eq, h_den_eq]
        norm_num
      rw [h_x] at hx
      revert hx
      norm_num





















