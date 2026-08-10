import FormalConjectures.Util.ProblemImports

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

theorem apery_poly_3_eq : apery_poly 3 = 1 + C 36 * X + C 90 * X ^ 2 + C 20 * X ^ 3 := by
  unfold apery_poly
  rfl

lemma eval_apery_poly_3 (x : ℚ) : eval x (apery_poly 3) = 20 * x ^ 3 + 90 * x ^ 2 + 36 * x + 1 := by
  rw [apery_poly_3_eq]
  simp [eval_add, eval_C, eval_mul, eval_pow, eval_X]
  ring

lemma eq_zero_of_eval_zero (x : ℚ) (h : 20 * x ^ 3 + 90 * x ^ 2 + 36 * x + 1 = 0) :
    20 * (x.num : ℚ) ^ 3 + 90 * (x.num : ℚ) ^ 2 * (x.den : ℚ) + 36 * (x.num : ℚ) * (x.den : ℚ) ^ 2 + (x.den : ℚ) ^ 3 = 0 := by
  set a : ℚ := (x.num : ℚ)
  set b : ℚ := (x.den : ℚ)
  have h_eq : x = a / b := by exact x.num_div_den.symm
  have h_den : b ≠ 0 := by
    dsimp [b]
    exact_mod_cast x.den_nz
  have h_mul : (20 * x ^ 3 + 90 * x ^ 2 + 36 * x + 1) * b ^ 3 = 0 := by
    rw [h, zero_mul]
  rw [h_eq] at h_mul
  have h_expand : (20 * (a / b) ^ 3 + 90 * (a / b) ^ 2 + 36 * (a / b) + 1) * b ^ 3 =
      20 * a ^ 3 + 90 * a ^ 2 * b + 36 * a * b ^ 2 + b ^ 3 := by
    field_simp [h_den]
  rw [h_expand] at h_mul
  exact h_mul

lemma eq_zero_of_eval_zero_int (x : ℚ) (h : 20 * x ^ 3 + 90 * x ^ 2 + 36 * x + 1 = 0) :
    20 * x.num ^ 3 + 90 * x.num ^ 2 * (x.den : ℤ) + 36 * x.num * (x.den : ℤ) ^ 2 + (x.den : ℤ) ^ 3 = 0 := by
  exact_mod_cast eq_zero_of_eval_zero x h

lemma a_dvd_two_c_pow_three (a c : ℤ) (h : 5 * a ^ 3 + 45 * a ^ 2 * c + 36 * a * c ^ 2 + 2 * c ^ 3 = 0) :
    a ∣ 2 * c ^ 3 := by
  have h_eq : 2 * c ^ 3 = - a * (5 * a ^ 2 + 45 * a * c + 36 * c ^ 2) := by
    linarith
  use (- (5 * a ^ 2 + 45 * a * c + 36 * c ^ 2))
  linarith

lemma c_dvd_five_a_pow_three (a c : ℤ) (h : 5 * a ^ 3 + 45 * a ^ 2 * c + 36 * a * c ^ 2 + 2 * c ^ 3 = 0) :
    c ∣ 5 * a ^ 3 := by
  have h_eq : 5 * a ^ 3 = - c * (45 * a ^ 2 + 36 * a * c + 2 * c ^ 2) := by
    linarith
  use (- (45 * a ^ 2 + 36 * a * c + 2 * c ^ 2))
  linarith






