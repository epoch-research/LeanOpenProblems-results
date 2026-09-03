import Submission.BinomialRowRigidity

/-! A global obstruction to separated two-block fourth powers. It does not
 cover dense or overlapping blocks and does not settle Erdős 406. -/
namespace Erdos406Work

lemma three_free_square_mod {a : ℕ} (ha : ¬ 3 ∣ a) : a ^ 2 % 3 = 1 := by
  have hne : a % 3 ≠ 0 := fun h => ha (Nat.dvd_of_mod_eq_zero h)
  have hlt := Nat.mod_lt a (by decide : 0 < 3)
  have hc : a % 3 = 1 ∨ a % 3 = 2 := by omega
  rcases hc with hc | hc <;> norm_num [Nat.pow_mod, hc]

/-- The constant coefficient and the middle coefficient of a scaled fourth
 power cannot both be ternary-good. This holds without any coprimality
 assumptions on the positive root blocks or scale. -/
lemma quartic_middle_coefficient_bad {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hgood : Nat.digits 3 (c * a ^ 4) ⊆ [0, 1]) :
    ¬ Nat.digits 3 (6 * c * a ^ 2 * b ^ 2) ⊆ [0, 1] := by
  obtain ⟨r, A, hA, heA⟩ := Nat.exists_eq_pow_mul_and_not_dvd (ne_of_gt ha) 3 (by decide)
  obtain ⟨s, B, hB, heB⟩ := Nat.exists_eq_pow_mul_and_not_dvd (ne_of_gt hb) 3 (by decide)
  obtain ⟨t, C, hC, heC⟩ := Nat.exists_eq_pow_mul_and_not_dvd (ne_of_gt hc) 3 (by decide)
  have hA2 := three_free_square_mod hA
  have hB2 := three_free_square_mod hB
  have hA4 : A ^ 4 % 3 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, Nat.pow_mod, hA2]
  have he0 : c * a ^ 4 = 3 ^ (t + r * 4) * (C * A ^ 4) := by
    rw [heA, heC]
    simp only [pow_add, pow_mul, mul_pow]
    ring
  rw [he0, good_mul_three_pow_iff] at hgood
  have hCmod : C % 3 = 1 := by
    have hh := ternary_digit_bound hgood 0
    norm_num only [pow_zero, Nat.div_one] at hh
    rw [Nat.mul_mod, hA4, mul_one, Nat.mod_mod] at hh
    have hn : C % 3 ≠ 0 := fun h => hC (Nat.dvd_of_mod_eq_zero h)
    omega
  have he2 : 6 * c * a ^ 2 * b ^ 2 =
      3 ^ (t + r * 2 + s * 2 + 1) * (2 * C * A ^ 2 * B ^ 2) := by
    rw [heA, heB, heC]
    simp only [pow_add, pow_mul, mul_pow, pow_one]
    ring
  intro hg
  rw [he2, good_mul_three_pow_iff] at hg
  have hh := ternary_digit_bound hg 0
  norm_num only [pow_zero, Nat.div_one] at hh
  norm_num [Nat.mul_mod, hCmod, hA2, hB2] at hh

/-- Only the first three coefficient bounds are needed. Once those blocks
 are separated, the forbidden middle coefficient cannot be hidden by carries. -/
theorem separated_scaled_fourth_power_bad {a b c L : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h0 : c * a ^ 4 < 3 ^ L)
    (h1 : 4 * c * a ^ 3 * b < 3 ^ L)
    (h2 : 6 * c * a ^ 2 * b ^ 2 < 3 ^ L) :
    ¬ Nat.digits 3 (c * (a + 3 ^ L * b) ^ 4) ⊆ [0, 1] := by
  have he : c * (a + 3 ^ L * b) ^ 4 =
      c * a ^ 4 + 3 ^ L * (4 * c * a ^ 3 * b +
        3 ^ L * (6 * c * a ^ 2 * b ^ 2 +
          3 ^ L * (4 * c * a * b ^ 3 + 3 ^ L * (c * b ^ 4)))) := by ring
  intro hg
  rw [he, good_split_iff h0, good_split_iff h1, good_split_iff h2] at hg
  exact quartic_middle_coefficient_bad ha hb hc hg.1 hg.2.2.1

#print axioms quartic_middle_coefficient_bad
#print axioms separated_scaled_fourth_power_bad
end Erdos406Work
