import Submission.ThirteenSixteenthPrimeBound

/-! An unconditional Jacobsthal bound of exponent 21/8, strictly improving the
11/4 bound but not settling the quadratic conjecture. -/
namespace Erdos970
open FiniteSelberg Real

noncomputable def thirteenSixteenthPowerConstant : ℕ := ⌈thirteenSixteenthBoundConstant⌉₊ + 1

lemma thirteenSixteenthPowerConstant_pos : 0 < thirteenSixteenthPowerConstant := Nat.succ_pos _

lemma thirteenSixteenthBoundConstant_lt : thirteenSixteenthBoundConstant < (thirteenSixteenthPowerConstant : ℝ) := by
  have hh := Nat.le_ceil thirteenSixteenthBoundConstant
  simp only [thirteenSixteenthPowerConstant, Nat.cast_add, Nat.cast_one]
  linarith

lemma exists_sixteenth_power_envelope (k : ℕ) (hk : 0 < k) :
    ∃ t : ℕ, 0 < t ∧ k ≤ t ^ 16 ∧ t ^ 16 ≤ 65536 * k := by
  have hex : ∃ t : ℕ, k ≤ t ^ 16 := ⟨k, Nat.le_pow (by omega)⟩
  let t := Nat.find hex
  have hkt : k ≤ t ^ 16 := Nat.find_spec hex
  have ht : 0 < t := by
    by_contra h
    have ht0 : t = 0 := by omega
    simp only [ht0, zero_pow (by omega : 16 ≠ 0)] at hkt
    omega
  refine ⟨t, ht, hkt, ?_⟩
  by_cases ht1 : t = 1
  · simp only [ht1, one_pow]
    omega
  · have hpred : (t - 1) ^ 16 < k := by
      have hh := Nat.find_min hex (show t - 1 < t by omega)
      omega
    have hh := Nat.pow_le_pow_left (show t ≤ 2 * (t - 1) by omega) 16
    rw [Nat.mul_pow] at hh
    norm_num only [show (2 : ℕ) ^ 16 = 65536 by norm_num] at hh
    exact hh.trans (Nat.mul_le_mul_left 65536 hpred.le)

/-- A bound on the sixteenth-power cardinality envelope. -/
theorem isJacobsthalBound_thirteen_sixteenths (k t : ℕ) (ht : 0 < t) (hkt : k ≤ t ^ 16) :
    IsJacobsthalBound k (thirteenSixteenthPowerConstant * t ^ 42) := by
  classical
  by_contra hbad
  obtain ⟨P, hP, hcard, r, hcover⟩ :=
    (not_isJacobsthalBound_iff_cover k (thirteenSixteenthPowerConstant * t ^ 42)).mp hbad
  have hm : thirteenSixteenthBoundConstant * (t : ℝ) ^ 42 < (thirteenSixteenthPowerConstant * t ^ 42 : ℕ) := by
    push_cast
    exact mul_lt_mul_of_pos_right thirteenSixteenthBoundConstant_lt (by positivity)
  obtain ⟨j, hj, havoid⟩ := prime_survivor_thirteen_sixteenths P hP t ht (hcard.trans hkt) r _ hm
  obtain ⟨p, hp, hjp⟩ := hcover j hj
  exact havoid p hp hjp

noncomputable def twentyOneEighthConstant : ℕ := thirteenSixteenthPowerConstant ^ 8 * 65536 ^ 21

lemma twentyOneEighthConstant_pos : 0 < twentyOneEighthConstant := by
  unfold twentyOneEighthConstant
  exact Nat.mul_pos (Nat.pow_pos thirteenSixteenthPowerConstant_pos) (by positivity)

/-- An integer-power statement of the exponent 21/8 bound. -/
theorem jacobsthalFunction_eighth_le_twenty_first (k : ℕ) (hk : 0 < k) :
    jacobsthalFunction k ^ 8 ≤ twentyOneEighthConstant * k ^ 21 := by
  obtain ⟨t, ht, hkt, htk⟩ := exists_sixteenth_power_envelope k hk
  have hh := (jacobsthalFunction_le_iff k _).mpr (isJacobsthalBound_thirteen_sixteenths k t ht hkt)
  have hpow := Nat.pow_le_pow_left hh 8
  have htkpow := Nat.pow_le_pow_left htk 21
  calc
    _ ≤ (thirteenSixteenthPowerConstant * t ^ 42) ^ 8 := hpow
    _ = thirteenSixteenthPowerConstant ^ 8 * (t ^ 16) ^ 21 := by ring
    _ ≤ thirteenSixteenthPowerConstant ^ 8 * (65536 * k) ^ 21 := Nat.mul_le_mul_left _ htkpow
    _ = twentyOneEighthConstant * k ^ 21 := by unfold twentyOneEighthConstant; ring

/-- The real-valued asymptotic exponent is 21/8, not two. -/
theorem exists_twenty_one_eighths_bound :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤ C * (k : ℝ) ^ ((21 : ℝ) / 8) := by
  let C : ℝ := (twentyOneEighthConstant : ℝ) + 1
  have hC : 1 ≤ C := by dsimp [C]; have := Nat.cast_nonneg (α := ℝ) twentyOneEighthConstant; linarith
  refine ⟨C, by linarith, ?_⟩
  intro k hk
  have hh : (jacobsthalFunction k : ℝ) ^ 8 ≤ (twentyOneEighthConstant : ℝ) * (k : ℝ) ^ 21 := by
    exact_mod_cast jacobsthalFunction_eighth_le_twenty_first k hk
  have he : ((k : ℝ) ^ ((21 : ℝ) / 8)) ^ 8 = (k : ℝ) ^ 21 := by
    rw [← Real.rpow_natCast _ 8, ← Real.rpow_mul (Nat.cast_nonneg k)]
    norm_num
  have hc : (twentyOneEighthConstant : ℝ) ≤ C ^ 8 := by
    have hc' : C ≤ C ^ 8 := by
      simpa only [pow_one] using (pow_le_pow_right₀ hC (by omega : 1 ≤ 8))
    dsimp [C] at *
    linarith
  apply (pow_le_pow_iff_left₀ (Nat.cast_nonneg (jacobsthalFunction k))
    (show 0 ≤ C * (k : ℝ) ^ ((21 : ℝ) / 8) by positivity) (by omega : 8 ≠ 0)).mp
  rw [mul_pow, he]
  exact hh.trans (mul_le_mul_of_nonneg_right hc (by positivity))

#print axioms isJacobsthalBound_thirteen_sixteenths
#print axioms jacobsthalFunction_eighth_le_twenty_first
#print axioms exists_twenty_one_eighths_bound
end Erdos970
