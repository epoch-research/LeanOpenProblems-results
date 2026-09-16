import Submission.Spec
import Mathlib

open Real
open scoped Set

lemma a_5 : a 5 = 4 := by
  dsimp [a]
  have h_sqrt2_pos : (0 : ℝ) < sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h1 : (3.5 : ℝ) ≤ 5 / sqrt 2 := by
    rw [le_div_iff₀ h_sqrt2_pos]
    have h_sq : (3.5 * sqrt 2) ^ 2 ≤ 5 ^ 2 := by
      calc (3.5 * sqrt 2) ^ 2 = 3.5 ^ 2 * 2 := by
             rw [mul_pow, sq_sqrt (by norm_num)]
           _ = 24.5 := by norm_num
           _ ≤ 25 := by norm_num
           _ = 5 ^ 2 := by norm_num
    have H : Real.sqrt ((3.5 * sqrt 2)^2) ≤ Real.sqrt (5^2) := Real.sqrt_le_sqrt h_sq
    rw [Real.sqrt_sq (by positivity), Real.sqrt_sq (by norm_num)] at H
    exact H
  have h2 : 5 / sqrt 2 < (4.5 : ℝ) := by
    rw [div_lt_iff₀ h_sqrt2_pos]
    have h_sq : (5 : ℝ) ^ 2 < (4.5 * sqrt 2) ^ 2 := by
      calc (5 : ℝ) ^ 2 = 25 := by norm_num
           _ < 40.5 := by norm_num
           _ = 4.5 ^ 2 * 2 := by norm_num
           _ = (4.5 * sqrt 2) ^ 2 := by
             rw [mul_pow, sq_sqrt (by norm_num)]
    have H : Real.sqrt (5^2) < Real.sqrt ((4.5 * sqrt 2)^2) := Real.sqrt_lt_sqrt (by norm_num) h_sq
    rw [Real.sqrt_sq (by norm_num), Real.sqrt_sq (by positivity)] at H
    exact H
  have h3 : (4 : ℝ) ≤ 5 / sqrt 2 + 1 / 2 := by linarith
  have h4 : 5 / sqrt 2 + 1 / 2 < (4 : ℝ) + 1 := by linarith
  have h5 : Int.floor (5 / sqrt 2 + 1 / 2) = 4 := Int.floor_eq_iff.mpr ⟨h3, h4⟩
  rw [h5]
  rfl

lemma a_4 : a 4 = 3 := by
  dsimp [a]
  have h_sqrt2_pos : (0 : ℝ) < sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h1 : (2.5 : ℝ) ≤ 4 / sqrt 2 := by
    rw [le_div_iff₀ h_sqrt2_pos]
    have h_sq : (2.5 * sqrt 2) ^ 2 ≤ 4 ^ 2 := by
      calc (2.5 * sqrt 2) ^ 2 = 2.5 ^ 2 * 2 := by
             rw [mul_pow, sq_sqrt (by norm_num)]
           _ = 12.5 := by norm_num
           _ ≤ 16 := by norm_num
           _ = 4 ^ 2 := by norm_num
    have H : Real.sqrt ((2.5 * sqrt 2)^2) ≤ Real.sqrt (4^2) := Real.sqrt_le_sqrt h_sq
    rw [Real.sqrt_sq (by positivity), Real.sqrt_sq (by norm_num)] at H
    exact H
  have h2 : 4 / sqrt 2 < (3.5 : ℝ) := by
    rw [div_lt_iff₀ h_sqrt2_pos]
    have h_sq : (4 : ℝ) ^ 2 < (3.5 * sqrt 2) ^ 2 := by
      calc (4 : ℝ) ^ 2 = 16 := by norm_num
           _ < 24.5 := by norm_num
           _ = 3.5 ^ 2 * 2 := by norm_num
           _ = (3.5 * sqrt 2) ^ 2 := by
             rw [mul_pow, sq_sqrt (by norm_num)]
    have H : Real.sqrt (4^2) < Real.sqrt ((3.5 * sqrt 2)^2) := Real.sqrt_lt_sqrt (by norm_num) h_sq
    rw [Real.sqrt_sq (by norm_num), Real.sqrt_sq (by positivity)] at H
    exact H
  have h3 : (3 : ℝ) ≤ 4 / sqrt 2 + 1 / 2 := by linarith
  have h4 : 4 / sqrt 2 + 1 / 2 < (3 : ℝ) + 1 := by linarith
  have h5 : Int.floor (4 / sqrt 2 + 1 / 2) = 3 := Int.floor_eq_iff.mpr ⟨h3, h4⟩
  rw [h5]
  rfl

lemma not_in_A001954 : 5 ∉ A001954 := by
  intro h
  rcases h with ⟨k, hk0, hk⟩
  have h5 : Int.floor ((k : ℝ) * phi) = 5 := by
    have hm : 0 ≤ Int.floor ((k : ℝ) * phi) := by
      dsimp [phi]
      have h_sqrt5_pos : (0 : ℝ) ≤ sqrt 5 := Real.sqrt_nonneg 5
      have h_nonneg : (0 : ℝ) ≤ (k : ℝ) * ((1 + sqrt 5) / 2) := by positivity
      exact Int.floor_nonneg.mpr h_nonneg
    have h_toNat : (Int.floor ((k : ℝ) * phi)).toNat = 5 := hk.symm
    zify at h_toNat
    rw [Int.toNat_of_nonneg hm] at h_toNat
    exact h_toNat
  have h_bounds : (5 : ℝ) ≤ (k : ℝ) * phi ∧ (k : ℝ) * phi < 6 := by
    have H1 : (5 : ℤ) ≤ Int.floor ((k : ℝ) * phi) := by rw [h5]
    have H2 : Int.floor ((k : ℝ) * phi) < (6 : ℤ) := by linarith
    constructor
    · exact Int.le_floor.mp H1
    · exact Int.floor_lt.mp H2
  rcases h_bounds with ⟨h_le, h_lt⟩
  have h_cases : k ≤ 3 ∨ 4 ≤ k := by omega
  rcases h_cases with hk3 | hk4
  · have h_k : (k : ℝ) ≤ 3 := Nat.cast_le.mpr hk3
    have h_lt5 : (k : ℝ) * phi < 5 := by
      calc (k : ℝ) * phi ≤ 3 * phi := by
             apply mul_le_mul_of_nonneg_right h_k
             dsimp [phi]; positivity
           _ = 1.5 + 1.5 * sqrt 5 := by
             dsimp [phi]; ring
           _ < 5 := by
             have h_sqrt : 1.5 * sqrt 5 < 3.5 := by
               have h_sq : (1.5 * sqrt 5) ^ 2 < 3.5 ^ 2 := by
                 calc (1.5 * sqrt 5) ^ 2 = 1.5 ^ 2 * 5 := by
                        rw [mul_pow, sq_sqrt (by norm_num)]
                      _ = 11.25 := by norm_num
                      _ < 12.25 := by norm_num
                      _ = 3.5 ^ 2 := by norm_num
               have H : Real.sqrt ((1.5 * sqrt 5)^2) < Real.sqrt (3.5^2) := Real.sqrt_lt_sqrt (by norm_num) h_sq
               rw [Real.sqrt_sq (by positivity), Real.sqrt_sq (by norm_num)] at H
               exact H
             linarith
    linarith
  · have h_k : (4 : ℝ) ≤ k := Nat.cast_le.mpr hk4
    have h_ge6 : 6 < (k : ℝ) * phi := by
      calc (6 : ℝ) < 4 * phi := by
             have h_sqrt : (4 : ℝ) < 2 * sqrt 5 := by
               have h_sq : (4 : ℝ) ^ 2 < (2 * sqrt 5) ^ 2 := by
                 calc (4 : ℝ) ^ 2 = 16 := by norm_num
                      _ < 20 := by norm_num
                      _ = 2 ^ 2 * 5 := by norm_num
                      _ = (2 * sqrt 5) ^ 2 := by
                        rw [mul_pow, sq_sqrt (by norm_num)]
               have H : Real.sqrt (4^2) < Real.sqrt ((2 * sqrt 5)^2) := Real.sqrt_lt_sqrt (by norm_num) h_sq
               rw [Real.sqrt_sq (by norm_num), Real.sqrt_sq (by positivity)] at H
               exact H
             dsimp [phi]; linarith
           _ ≤ (k : ℝ) * phi := by
             apply mul_le_mul_of_nonneg_right h_k
             dsimp [phi]; positivity
    linarith

theorem disproof_check : ¬ (type_of% @oeis_49473_conjecture_0) := by
  intro h
  rcases h with ⟨_, h2⟩
  have h5 := h2 5 (by decide)
  dsimp at h5
  have h_a5 : a 5 = 4 := a_5
  have h_a4 : a 4 = 3 := a_4
  have h_sub : a 5 - a (5 - 1) = 1 := by
    have : 5 - 1 = 4 := rfl
    rw [this, h_a5, h_a4]
  rw [h_sub] at h5
  rcases h5 with ⟨h_iff, _⟩
  have h_in : 5 ∈ A001954 := h_iff.mp rfl
  exact not_in_A001954 h_in
