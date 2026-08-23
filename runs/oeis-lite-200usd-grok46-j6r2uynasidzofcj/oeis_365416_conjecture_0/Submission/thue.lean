import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

open Int

def thueF (a b : ℤ) : ℤ := a ^ 3 + 3 * a ^ 2 * b + 6 * a * b ^ 2 + 2 * b ^ 3

def Fkb (k b : ℤ) : ℤ := k ^ 3 + 3 * k * b ^ 2 - 2 * b ^ 3

lemma thueF_eq_Fkb (a b : ℤ) : thueF a b = Fkb (a + b) b := by
  simp [thueF, Fkb]; ring

lemma thueF_neg (a b : ℤ) : thueF (-a) (-b) = -thueF a b := by
  simp [thueF]; ring

lemma cube_eq_one {a : ℤ} (h : a ^ 3 = 1) : a = 1 := by
  have htr : a ≤ 0 ∨ a = 1 ∨ 2 ≤ a := by omega
  rcases htr with h1 | h1 | h1
  · have : a ^ 3 ≤ 0 := by
      exact pow_nonpos (n := 3) h1 (by decide)
    omega
  · exact h1
  · have : (8 : ℤ) ≤ a ^ 3 := by
      have : (2 : ℤ) ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ (by omega) h1 3
      simpa using this
    omega

lemma cube_eq_neg_one {a : ℤ} (h : a ^ 3 = -1) : a = -1 := by
  have htr : a ≤ -2 ∨ a = -1 ∨ 0 ≤ a := by omega
  rcases htr with h1 | h1 | h1
  · have : a ^ 3 ≤ (-2 : ℤ) ^ 3 :=
      pow_le_pow_left_of_nonpos (by decide) (by omega) (by decide : 0 < 3)
    have : a ^ 3 ≤ -8 := this
    omega
  · exact h1
  · have : 0 ≤ a ^ 3 := pow_nonneg h1 3
    omega

lemma abs_Fkb_k0 {b : ℤ} (hb : b ≠ 0) : 2 ≤ |Fkb 0 b| := by
  simp [Fkb]
  have : 1 ≤ |b| := abs_pos.mpr hb
  have : 1 ≤ |b| ^ 3 := one_le_pow₀ this
  have : |(-2) * b ^ 3| = 2 * |b| ^ 3 := by
    rw [abs_mul, abs_neg, abs_two, abs_pow]
  nlinarith

lemma abs_Fkb_k1 {b : ℤ} (hb : b ≠ 0) : 2 ≤ |Fkb 1 b| := by
  simp only [Fkb, one_pow, one_mul]
  have : b ≤ -1 ∨ 1 ≤ b := by omega
  rcases this with hb1 | hb1
  · have : 1 + 3 * b ^ 2 - 2 * b ^ 3 = 1 + 3 * b ^ 2 + 2 * (-b) ^ 3 := by ring
    rw [this]
    have hnb : (1 : ℤ) ≤ -b := by omega
    have : (1 : ℤ) ≤ (-b) ^ 3 := one_le_pow₀ hnb
    have : (1 : ℤ) ≤ b ^ 2 := by
      nlinarith [sq_nonneg b]
    have hge : (6 : ℤ) ≤ 1 + 3 * b ^ 2 + 2 * (-b) ^ 3 := by nlinarith
    rw [abs_of_nonneg (by nlinarith)]
    linarith
  · have hb' : b = 1 ∨ 2 ≤ b := by omega
    rcases hb' with rfl | hb2
    · norm_num
    · have : 1 + 3 * b ^ 2 - 2 * b ^ 3 ≤ -3 := by
        nlinarith [sq_nonneg (b - 2)]
      rw [abs_of_nonpos (by linarith)]
      linarith

lemma abs_Fkb_kneg1 {b : ℤ} (hb : b ≠ 0) : 2 ≤ |Fkb (-1) b| := by
  have heq : Fkb (-1) b = -(2 * b ^ 3 + 3 * b ^ 2 + 1) := by simp [Fkb]; ring
  rw [heq, abs_neg]
  have : b ≤ -1 ∨ 1 ≤ b := by omega
  rcases this with hb1 | hb1
  · have hb' : b = -1 ∨ b ≤ -2 := by omega
    rcases hb' with rfl | hb2
    · norm_num
    · have : 2 * b ^ 3 + 3 * b ^ 2 + 1 ≤ -3 := by
        nlinarith [sq_nonneg (b + 2)]
      rw [abs_of_nonpos (by linarith)]
      linarith
  · have : (6 : ℤ) ≤ 2 * b ^ 3 + 3 * b ^ 2 + 1 := by
      nlinarith [one_le_pow₀ hb1]
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- `|b| ≥ 2|k|` and `|k| ≥ 2` implies `|F| ≥ 2`. -/
lemma abs_Fkb_b_ge_two_k {k b : ℤ} (hk : 2 ≤ |k|) (hb : 2 * |k| ≤ |b|) :
    2 ≤ |Fkb k b| := by
  have hb2 : b ^ 2 = |b| ^ 2 := (sq_abs b).symm
  have hdecomp : 2 * |b| ^ 3 - 3 * |k| * b ^ 2 = |b| ^ 2 * (2 * |b| - 3 * |k|) := by
    rw [hb2]; ring
  have hdiff : (2 : ℤ) ≤ 2 * |b| - 3 * |k| := by nlinarith
  have hpos : 0 ≤ 2 * |b| - 3 * |k| := by nlinarith
  have hge : |b| ^ 2 * (2 * |b| - 3 * |k|) - |k| ^ 3 ≥ 3 * |k| ^ 3 := by
    have : (4 : ℤ) * |k| ^ 2 ≤ |b| ^ 2 := by
      have : (2 * |k|) ^ 2 ≤ |b| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
      have : (2 * |k|) ^ 2 = 4 * |k| ^ 2 := by ring
      linarith
    nlinarith
  have : |Fkb k b| ≥ 2 * |b| ^ 3 - |k| ^ 3 - 3 * |k| * b ^ 2 := by
    have h1 : |2 * b ^ 3| = 2 * |b| ^ 3 := by rw [abs_mul, abs_two, abs_pow]
    have h2 : |k ^ 3| = |k| ^ 3 := abs_pow k 3
    have h3 : |3 * k * b ^ 2| = 3 * |k| * b ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nat]
      simp [abs_of_nonneg (sq_nonneg b)]
      ring
    have := abs_sub_abs_le_abs_sub (2 * b ^ 3) (k ^ 3 + 3 * k * b ^ 2)
    -- |2b^3| - |k^3+3kb^2| ≤ |2b^3 - (k^3+3kb^2)| = |Fkb|  (up to sign)
    have hF : |Fkb k b| = |2 * b ^ 3 - (k ^ 3 + 3 * k * b ^ 2)| := by
      simp [Fkb]; congr 1; ring
    have : |2 * b ^ 3| - |k ^ 3 + 3 * k * b ^ 2| ≤ |2 * b ^ 3 - (k ^ 3 + 3 * k * b ^ 2)| :=
      abs_sub_abs_le_abs_sub _ _
    have : |k ^ 3 + 3 * k * b ^ 2| ≤ |k ^ 3| + |3 * k * b ^ 2| := abs_add _ _
    rw [hF]
    linarith
  have : 3 * |k| ^ 3 ≥ 24 := by
    have : (8 : ℤ) ≤ |k| ^ 3 := by
      have : (2 : ℤ) ^ 3 ≤ |k| ^ 3 := pow_le_pow_left₀ (by decide) hk 3
      simpa using this
    nlinarith
  nlinarith

