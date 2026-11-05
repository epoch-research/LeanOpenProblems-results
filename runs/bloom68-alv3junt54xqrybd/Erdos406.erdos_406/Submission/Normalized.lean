import Submission.Arithmetic

/-! # Normalized ternary blocks of cubic iterates of four -/

namespace Erdos406.Normalized

theorem normalized_block (a : ℕ) (ha : 0 < a) :
    ∃ u : ℕ, (4 : ℕ) ^ (3 ^ a) = 1 + 3 ^ (a + 1) * u ∧ u % 9 = 7 := by
  induction a, ha using Nat.le_induction with
  | base => exact ⟨7, by norm_num, by decide⟩
  | succ a ha ih =>
    obtain ⟨u, hu, humod⟩ := ih
    let v := u + 3 ^ (a + 1) * (u ^ 2 + 3 ^ a * u ^ 3)
    refine ⟨v, ?_, ?_⟩
    · calc
        (4 : ℕ) ^ (3 ^ (a + 1)) = ((4 : ℕ) ^ (3 ^ a)) ^ 3 := by
          rw [pow_succ, pow_mul]
        _ = (1 + 3 ^ (a + 1) * u) ^ 3 := by rw [hu]
        _ = 1 + 3 ^ (a + 1 + 1) * v := by
          dsimp [v]
          simp only [pow_succ]
          ring
    · have hdiv : 9 ∣ (3 : ℕ) ^ (a + 1) := by
        change (3 : ℕ) ^ 2 ∣ (3 : ℕ) ^ (a + 1)
        exact Nat.pow_dvd_pow 3 (by omega)
      have hzero : (3 : ℕ) ^ (a + 1) % 9 = 0 := Nat.mod_eq_zero_of_dvd hdiv
      dsimp [v]
      simp [Nat.add_mod, Nat.mul_mod, hzero, humod]

theorem cubic_iterate_digit (a : ℕ) (ha : 0 < a) :
    (4 : ℕ) ^ (3 ^ a) / 3 ^ (a + 2) % 3 = 2 := by
  obtain ⟨u, hu, humod⟩ := normalized_block a ha
  have hp : 1 < (3 : ℕ) ^ (a + 1) := by
    exact Nat.one_lt_pow (by omega) (by decide)
  have hdiv : (4 : ℕ) ^ (3 ^ a) / 3 ^ (a + 1) = u := by
    rw [hu, Nat.add_mul_div_left _ _ (by omega)]
    rw [Nat.div_eq_of_lt hp, zero_add]
  have hquot : (4 : ℕ) ^ (3 ^ a) / 3 ^ (a + 2) = u / 3 := by
    rw [show a + 2 = (a + 1) + 1 by omega, pow_succ,
      ← Nat.div_div_eq_div_mul, hdiv]
  rw [hquot]
  omega

theorem cubic_iterate_has_digit_two (a : ℕ) (ha : 0 < a) :
    2 ∈ Nat.digits 3 ((4 : ℕ) ^ (3 ^ a)) := by
  by_contra h
  have hgood := (Arithmetic.digits_good_iff_two_absent _).mpr h
  exact Arithmetic.digits_good_digit_ne_two _ (a + 2) hgood (cubic_iterate_digit a ha)

theorem exponent_two_times_three_pow_bad (a : ℕ) (ha : 0 < a) :
    ¬ Arithmetic.goodExponent (2 * 3 ^ a) := by
  have heq : (2 : ℕ) ^ (2 * 3 ^ a) = (4 : ℕ) ^ (3 ^ a) := by
    rw [pow_mul]
    norm_num
  intro hg
  change Nat.digits 3 (2 ^ (2 * 3 ^ a)) ⊆ [0, 1] at hg
  rw [heq] at hg
  exact (Arithmetic.digits_good_iff_two_absent _).mp hg (cubic_iterate_has_digit_two a ha)

end Erdos406.Normalized
