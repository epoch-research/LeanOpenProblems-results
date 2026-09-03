import Submission.SevenEighthPrimeBound

/-! An unconditional Jacobsthal bound of exponent 11/4, strictly improving the
cubic bound but not settling the quadratic conjecture. -/
namespace Erdos970
open FiniteSelberg Real

noncomputable def sevenEighthPowerConstant : ℕ := ⌈sevenEighthBoundConstant⌉₊ + 1

lemma sevenEighthPowerConstant_pos : 0 < sevenEighthPowerConstant := Nat.succ_pos _

lemma sevenEighthBoundConstant_lt : sevenEighthBoundConstant < (sevenEighthPowerConstant : ℝ) := by
  have hh := Nat.le_ceil sevenEighthBoundConstant
  simp only [sevenEighthPowerConstant, Nat.cast_add, Nat.cast_one]
  linarith

lemma exists_eighth_power_envelope (k : ℕ) (hk : 0 < k) :
    ∃ t : ℕ, 0 < t ∧ k ≤ t ^ 8 ∧ t ^ 8 ≤ 256 * k := by
  have hex : ∃ t : ℕ, k ≤ t ^ 8 := ⟨k, Nat.le_pow (by omega)⟩
  let t := Nat.find hex
  have hkt : k ≤ t ^ 8 := Nat.find_spec hex
  have ht : 0 < t := by
    by_contra h
    have ht0 : t = 0 := by omega
    simp only [ht0, zero_pow (by omega : 8 ≠ 0)] at hkt
    omega
  refine ⟨t, ht, hkt, ?_⟩
  by_cases ht1 : t = 1
  · simp only [ht1, one_pow]
    omega
  · have hpred : (t - 1) ^ 8 < k := by
      have hh := Nat.find_min hex (show t - 1 < t by omega)
      omega
    have hh := Nat.pow_le_pow_left (show t ≤ 2 * (t - 1) by omega) 8
    rw [Nat.mul_pow] at hh
    norm_num only [show (2 : ℕ) ^ 8 = 256 by norm_num] at hh
    exact hh.trans (Nat.mul_le_mul_left 256 hpred.le)

/-- A bound on the eighth-power cardinality envelope. -/
theorem isJacobsthalBound_seven_eighths (k t : ℕ) (ht : 0 < t) (hkt : k ≤ t ^ 8) :
    IsJacobsthalBound k (sevenEighthPowerConstant * t ^ 22) := by
  classical
  by_contra hbad
  obtain ⟨P, hP, hcard, r, hcover⟩ :=
    (not_isJacobsthalBound_iff_cover k (sevenEighthPowerConstant * t ^ 22)).mp hbad
  have hm : sevenEighthBoundConstant * (t : ℝ) ^ 22 < (sevenEighthPowerConstant * t ^ 22 : ℕ) := by
    push_cast
    exact mul_lt_mul_of_pos_right sevenEighthBoundConstant_lt (by positivity)
  obtain ⟨j, hj, havoid⟩ := prime_survivor_seven_eighths P hP t ht (hcard.trans hkt) r _ hm
  obtain ⟨p, hp, hjp⟩ := hcover j hj
  exact havoid p hp hjp

noncomputable def elevenFourthConstant : ℕ := sevenEighthPowerConstant ^ 4 * 256 ^ 11

lemma elevenFourthConstant_pos : 0 < elevenFourthConstant := by
  unfold elevenFourthConstant
  exact Nat.mul_pos (Nat.pow_pos sevenEighthPowerConstant_pos) (by positivity)

/-- An integer-power statement of the exponent 11/4 bound. -/
theorem jacobsthalFunction_fourth_le_eleventh (k : ℕ) (hk : 0 < k) :
    jacobsthalFunction k ^ 4 ≤ elevenFourthConstant * k ^ 11 := by
  obtain ⟨t, ht, hkt, htk⟩ := exists_eighth_power_envelope k hk
  have hh := (jacobsthalFunction_le_iff k _).mpr (isJacobsthalBound_seven_eighths k t ht hkt)
  have hpow := Nat.pow_le_pow_left hh 4
  have htkpow := Nat.pow_le_pow_left htk 11
  calc
    _ ≤ (sevenEighthPowerConstant * t ^ 22) ^ 4 := hpow
    _ = sevenEighthPowerConstant ^ 4 * (t ^ 8) ^ 11 := by ring
    _ ≤ sevenEighthPowerConstant ^ 4 * (256 * k) ^ 11 := Nat.mul_le_mul_left _ htkpow
    _ = elevenFourthConstant * k ^ 11 := by unfold elevenFourthConstant; ring

/-- The real-valued asymptotic exponent is 11/4, not two. -/
theorem exists_eleven_fourths_bound :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤ C * (k : ℝ) ^ ((11 : ℝ) / 4) := by
  let C : ℝ := (elevenFourthConstant : ℝ) + 1
  have hC : 1 ≤ C := by dsimp [C]; have := Nat.cast_nonneg (α := ℝ) elevenFourthConstant; linarith
  refine ⟨C, by linarith, ?_⟩
  intro k hk
  have hh : (jacobsthalFunction k : ℝ) ^ 4 ≤ (elevenFourthConstant : ℝ) * (k : ℝ) ^ 11 := by
    exact_mod_cast jacobsthalFunction_fourth_le_eleventh k hk
  have he : ((k : ℝ) ^ ((11 : ℝ) / 4)) ^ 4 = (k : ℝ) ^ 11 := by
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul (Nat.cast_nonneg k)]
    norm_num
  have hc : (elevenFourthConstant : ℝ) ≤ C ^ 4 := by
    have hc' : C ≤ C ^ 4 := by
      simpa only [pow_one] using (pow_le_pow_right₀ hC (by omega : 1 ≤ 4))
    dsimp [C] at *
    linarith
  apply (pow_le_pow_iff_left₀ (Nat.cast_nonneg (jacobsthalFunction k))
    (show 0 ≤ C * (k : ℝ) ^ ((11 : ℝ) / 4) by positivity) (by omega : 4 ≠ 0)).mp
  rw [mul_pow, he]
  exact hh.trans (mul_le_mul_of_nonneg_right hc (by positivity))

#print axioms isJacobsthalBound_seven_eighths
#print axioms jacobsthalFunction_fourth_le_eleventh
#print axioms exists_eleven_fourths_bound
end Erdos970
