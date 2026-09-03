import Submission.HardCubicPrimeBound

/-! An unconditional Jacobsthal bound of exponent 5/2, strictly improving the
21/8 bound but not settling the quadratic conjecture. -/
namespace Erdos970
open FiniteSelberg Real

noncomputable def hardCubicPowerConstant : ℕ := ⌈hardCubicBoundConstant⌉₊ + 1

lemma hardCubicPowerConstant_pos : 0 < hardCubicPowerConstant := Nat.succ_pos _

lemma hardCubicBoundConstant_lt : hardCubicBoundConstant < (hardCubicPowerConstant : ℝ) := by
  have hh := Nat.le_ceil hardCubicBoundConstant
  simp only [hardCubicPowerConstant, Nat.cast_add, Nat.cast_one]
  linarith

lemma exists_fourth_power_envelope (k : ℕ) (hk : 0 < k) :
    ∃ t : ℕ, 0 < t ∧ k ≤ t ^ 4 ∧ t ^ 4 ≤ 16 * k := by
  have hex : ∃ t : ℕ, k ≤ t ^ 4 := ⟨k, Nat.le_pow (by omega)⟩
  let t := Nat.find hex
  have hkt : k ≤ t ^ 4 := Nat.find_spec hex
  have ht : 0 < t := by
    by_contra h
    have ht0 : t = 0 := by omega
    simp only [ht0, zero_pow (by omega : 4 ≠ 0)] at hkt
    omega
  refine ⟨t, ht, hkt, ?_⟩
  by_cases ht1 : t = 1
  · simp only [ht1, one_pow]
    omega
  · have hpred : (t - 1) ^ 4 < k := by
      have hh := Nat.find_min hex (show t - 1 < t by omega)
      omega
    have hh := Nat.pow_le_pow_left (show t ≤ 2 * (t - 1) by omega) 4
    rw [Nat.mul_pow] at hh
    norm_num only [show (2 : ℕ) ^ 4 = 16 by norm_num] at hh
    exact hh.trans (Nat.mul_le_mul_left 16 hpred.le)

/-- A bound on the fourth-power cardinality envelope. -/
theorem isJacobsthalBound_three_quarters (k t : ℕ) (ht : 0 < t) (hkt : k ≤ t ^ 4) :
    IsJacobsthalBound k (hardCubicPowerConstant * t ^ 10) := by
  classical
  by_contra hbad
  obtain ⟨P, hP, hcard, r, hcover⟩ :=
    (not_isJacobsthalBound_iff_cover k (hardCubicPowerConstant * t ^ 10)).mp hbad
  have hm : hardCubicBoundConstant * (t : ℝ) ^ 10 < (hardCubicPowerConstant * t ^ 10 : ℕ) := by
    push_cast
    exact mul_lt_mul_of_pos_right hardCubicBoundConstant_lt (by positivity)
  obtain ⟨j, hj, havoid⟩ := prime_survivor_three_quarters P hP t ht (hcard.trans hkt) r _ hm
  obtain ⟨p, hp, hjp⟩ := hcover j hj
  exact havoid p hp hjp

noncomputable def fiveHalvesConstant : ℕ := hardCubicPowerConstant ^ 2 * 16 ^ 5

lemma fiveHalvesConstant_pos : 0 < fiveHalvesConstant := by
  unfold fiveHalvesConstant
  exact Nat.mul_pos (Nat.pow_pos hardCubicPowerConstant_pos) (by positivity)

/-- An integer-power statement of the exponent 5/2 bound. -/
theorem jacobsthalFunction_sq_le_fifth (k : ℕ) (hk : 0 < k) :
    jacobsthalFunction k ^ 2 ≤ fiveHalvesConstant * k ^ 5 := by
  obtain ⟨t, ht, hkt, htk⟩ := exists_fourth_power_envelope k hk
  have hh := (jacobsthalFunction_le_iff k _).mpr (isJacobsthalBound_three_quarters k t ht hkt)
  have hpow := Nat.pow_le_pow_left hh 2
  have htkpow := Nat.pow_le_pow_left htk 5
  calc
    _ ≤ (hardCubicPowerConstant * t ^ 10) ^ 2 := hpow
    _ = hardCubicPowerConstant ^ 2 * (t ^ 4) ^ 5 := by ring
    _ ≤ hardCubicPowerConstant ^ 2 * (16 * k) ^ 5 := Nat.mul_le_mul_left _ htkpow
    _ = fiveHalvesConstant * k ^ 5 := by unfold fiveHalvesConstant; ring

/-- The real-valued asymptotic exponent is 5/2, not two. -/
theorem exists_five_halves_bound :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤ C * (k : ℝ) ^ ((5 : ℝ) / 2) := by
  let C : ℝ := (fiveHalvesConstant : ℝ) + 1
  have hC : 1 ≤ C := by dsimp [C]; have := Nat.cast_nonneg (α := ℝ) fiveHalvesConstant; linarith
  refine ⟨C, by linarith, ?_⟩
  intro k hk
  have hh : (jacobsthalFunction k : ℝ) ^ 2 ≤ (fiveHalvesConstant : ℝ) * (k : ℝ) ^ 5 := by
    exact_mod_cast jacobsthalFunction_sq_le_fifth k hk
  have he : ((k : ℝ) ^ ((5 : ℝ) / 2)) ^ 2 = (k : ℝ) ^ 5 := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (Nat.cast_nonneg k)]
    norm_num
  have hc : (fiveHalvesConstant : ℝ) ≤ C ^ 2 := by
    have hc' : C ≤ C ^ 2 := by
      simpa only [pow_one] using (pow_le_pow_right₀ hC (by omega : 1 ≤ 2))
    dsimp [C] at *
    linarith
  apply (pow_le_pow_iff_left₀ (Nat.cast_nonneg (jacobsthalFunction k))
    (show 0 ≤ C * (k : ℝ) ^ ((5 : ℝ) / 2) by positivity) (by omega : 2 ≠ 0)).mp
  rw [mul_pow, he]
  exact hh.trans (mul_le_mul_of_nonneg_right hc (by positivity))

#print axioms isJacobsthalBound_three_quarters
#print axioms jacobsthalFunction_sq_le_fifth
#print axioms exists_five_halves_bound
end Erdos970
