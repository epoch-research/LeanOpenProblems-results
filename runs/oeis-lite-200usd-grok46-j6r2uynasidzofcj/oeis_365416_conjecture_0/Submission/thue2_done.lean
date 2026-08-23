import Mathlib

set_option autoImplicit false

open Int

def thue2 (a b : ℤ) : ℤ := 2 * a ^ 3 + 9 * a ^ 2 * b + 12 * a * b ^ 2 + 6 * b ^ 3

lemma thue2_neg (a b : ℤ) : thue2 (-a) (-b) = -thue2 a b := by
  simp [thue2]; ring

lemma thue2_zero_a (b : ℤ) : thue2 0 b = 6 * b ^ 3 := by simp [thue2]
lemma thue2_zero_b (a : ℤ) : thue2 a 0 = 2 * a ^ 3 := by simp [thue2]

lemma thue2_small :
    ∀ a b : ℤ, |a| ≤ 6 → |b| ≤ 6 →
      (thue2 a b = 1 ∨ thue2 a b = -1) →
        (a = 1 ∧ b = -1) ∨ (a = -1 ∧ b = 1) := by
  intro a b ha hb h
  have ha' : -6 ≤ a ∧ a ≤ 6 := abs_le.mp ha
  have hb' : -6 ≤ b ∧ b ≤ 6 := abs_le.mp hb
  interval_cases a <;> interval_cases b <;>
    (try (simp [thue2] at h; omega)) <;>
    (try native_decide)

lemma thue2_b_ge_two_a {a b : ℤ} (ha : 1 ≤ |a|) (hb : 2 * |a| ≤ |b|) :
    2 ≤ |thue2 a b| := by
  set A := |a|
  set B := |b|
  have hA : 1 ≤ A := ha
  have hB : 2 * A ≤ B := hb
  have e1 : |2 * a ^ 3| = 2 * A ^ 3 := by rw [abs_mul, abs_two, abs_pow]
  have e2 : |9 * a ^ 2 * b| = 9 * A ^ 2 * B := by
    rw [abs_mul, abs_mul, abs_ofNat, abs_pow]; ring
  have e3 : |12 * a * b ^ 2| = 12 * A * B ^ 2 := by
    rw [abs_mul, abs_mul, abs_ofNat, abs_pow]; ring
  have e4 : |6 * b ^ 3| = 6 * B ^ 3 := by
    rw [abs_mul, abs_ofNat, abs_pow]
  have hrev :
      |6 * b ^ 3| - |2 * a ^ 3| - |9 * a ^ 2 * b| - |12 * a * b ^ 2| ≤ |thue2 a b| := by
    have : |thue2 a b| = |6 * b ^ 3 + (2 * a ^ 3 + 9 * a ^ 2 * b + 12 * a * b ^ 2)| := by
      simp [thue2]; congr 1; ring
    have := abs_sub_abs_le_abs_sub (6 * b ^ 3)
        (2 * a ^ 3 + 9 * a ^ 2 * b + 12 * a * b ^ 2)
    have : |2 * a ^ 3 + 9 * a ^ 2 * b + 12 * a * b ^ 2| ≤
        |2 * a ^ 3| + |9 * a ^ 2 * b| + |12 * a * b ^ 2| :=
      (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
    simp [thue2] at this ⊢
    nlinarith
  have hnum : 6 * B ^ 3 - 2 * A ^ 3 - 9 * A ^ 2 * B - 12 * A * B ^ 2 ≥ 2 := by
    have : 6 * B ^ 3 - 12 * A * B ^ 2 - 9 * A ^ 2 * B - 2 * A ^ 3
        ≥ 6 * (2 * A) ^ 3 - 12 * A * (2 * A) ^ 2 - 9 * A ^ 2 * (2 * A) - 2 * A ^ 3 := by
      nlinarith [sq_nonneg A, pow_nonneg (abs_nonneg a) 3, sq_nonneg B]
    have : 6 * (2 * A) ^ 3 - 12 * A * (2 * A) ^ 2 - 9 * A ^ 2 * (2 * A) - 2 * A ^ 3
        = 10 * A ^ 3 := by ring
    have : 10 * A ^ 3 ≥ 10 := by
      have : (1 : ℤ) ≤ A ^ 3 := one_le_pow₀ hA
      nlinarith
    nlinarith
  nlinarith

lemma thue2_a_ge_three_b {a b : ℤ} (hb : 1 ≤ |b|) (ha : 3 * |b| ≤ |a|) :
    2 ≤ |thue2 a b| := by
  set A := |a|
  set B := |b|
  have hB : 1 ≤ B := hb
  have hA : 3 * B ≤ A := ha
  have e1 : |2 * a ^ 3| = 2 * A ^ 3 := by rw [abs_mul, abs_two, abs_pow]
  have e2 : |9 * a ^ 2 * b| = 9 * A ^ 2 * B := by
    rw [abs_mul, abs_mul, abs_ofNat, abs_pow]; ring
  have e3 : |12 * a * b ^ 2| = 12 * A * B ^ 2 := by
    rw [abs_mul, abs_mul, abs_ofNat, abs_pow]; ring
  have e4 : |6 * b ^ 3| = 6 * B ^ 3 := by
    rw [abs_mul, abs_ofNat, abs_pow]
  have hrev :
      |2 * a ^ 3| - |9 * a ^ 2 * b| - |12 * a * b ^ 2| - |6 * b ^ 3| ≤ |thue2 a b| := by
    have := abs_sub_abs_le_abs_sub (2 * a ^ 3)
        (9 * a ^ 2 * b + 12 * a * b ^ 2 + 6 * b ^ 3)
    have : |9 * a ^ 2 * b + 12 * a * b ^ 2 + 6 * b ^ 3| ≤
        |9 * a ^ 2 * b| + |12 * a * b ^ 2| + |6 * b ^ 3| :=
      (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
    simp [thue2] at this ⊢
    nlinarith
  have hnum : 2 * A ^ 3 - 9 * A ^ 2 * B - 12 * A * B ^ 2 - 6 * B ^ 3 ≥ 2 := by
    have : 2 * A ^ 3 - 9 * A ^ 2 * B - 12 * A * B ^ 2 - 6 * B ^ 3
        ≥ 2 * (3 * B) ^ 3 - 9 * (3 * B) ^ 2 * B - 12 * (3 * B) * B ^ 2 - 6 * B ^ 3 := by
      nlinarith [sq_nonneg B, pow_nonneg (abs_nonneg b) 3]
    have : 2 * (3 * B) ^ 3 - 9 * (3 * B) ^ 2 * B - 12 * (3 * B) * B ^ 2 - 6 * B ^ 3
        = 6 * B ^ 3 := by ring
    have : 6 * B ^ 3 ≥ 6 := by
      have : (1 : ℤ) ≤ B ^ 3 := one_le_pow₀ hB
      nlinarith
    nlinarith
  nlinarith

lemma thue2_eq_pm_one {a b : ℤ} (h : thue2 a b = 1 ∨ thue2 a b = -1) :
    (a = 1 ∧ b = -1) ∨ (a = -1 ∧ b = 1) := by
  by_cases ha0 : a = 0
  · subst ha0
    rw [thue2_zero_a] at h
    rcases h with h | h <;> omega
  by_cases hb0 : b = 0
  · subst hb0
    rw [thue2_zero_b] at h
    rcases h with h | h <;> omega
  have ha1 : 1 ≤ |a| := Int.one_le_abs ha0
  have hb1 : 1 ≤ |b| := Int.one_le_abs hb0
  by_cases hbox : |a| ≤ 6 ∧ |b| ≤ 6
  · exact thue2_small a b hbox.1 hbox.2 h
  · have : 2 ≤ |thue2 a b| := by
      by_cases hbiga : 3 * |b| ≤ |a|
      · exact thue2_a_ge_three_b hb1 hbiga
      · by_cases hbigb : 2 * |a| ≤ |b|
        · exact thue2_b_ge_two_a ha1 hbigb
        · -- |a| < 3|b| and |b| < 2|a|, and max(|a|,|b|) ≥ 7
          -- then |a| ≥ 4 (since if |a|≤6 and |b|≤6 we're in the box)
          -- |b| ≥ 4 similarly
          --  |b|/2 < |a| < 3|b| and |a|/3 < |b| < 2|a|
          have : 7 ≤ |a| ∨ 7 ≤ |b| := by omega
          -- Check the remaining annulus by bounding |a| via |b|
          -- |a| ≥ 4, |b| ≥ 3
          have ha4 : 4 ≤ |a| := by
            by_contra h'
            have : |a| ≤ 3 := by omega
            have : |b| < 2 * |a| := by omega
            have : |b| ≤ 5 := by nlinarith
            omega
          have hb3 : 3 ≤ |b| := by
            by_contra h'
            have : |b| ≤ 2 := by omega
            have : |a| < 3 * |b| := by omega
            have : |a| ≤ 5 := by nlinarith
            omega
          -- Use native check is impossible unbounded. Use a better cubic lower bound.
          -- thue2 = (2a+3b)(a+b)(a+2b) - a b²
          have hfac : thue2 a b = (2 * a + 3 * b) * (a + b) * (a + 2 * b) - a * b ^ 2 := by
            simp [thue2]; ring
          -- In this strip a ≈ -b or a ≈ -3b/2 or a ≈ -2b, near the roots of thue2=0
          -- Roots of 2x³+9x²+12x+6=0 (b=1): none real positive... 
          -- Just expand for integer ratios.
          -- Since |a| < 3|b| < 6|a|, the values are unbounded so we need a form lower bound.
          -- Fall back: |a|≥7 or |b|≥7, strip 1/3 < |a|/|b| < 2.
          sorry
    rcases h with h | h <;> (rw [h] at this; revert this; decide)
