import Submission.SelbergCubicPrimeBound

/-! A uniform cubic Jacobsthal bound. This strengthens the earlier
fixed-power bound but is not the conjectured quadratic theorem. -/
namespace Erdos970
open FiniteSelberg

noncomputable def cubicPowerConstant : ℕ := ⌈cubicBoundConstant⌉₊ + 1

lemma cubicPowerConstant_pos : 0 < cubicPowerConstant := Nat.succ_pos _

lemma cubicBoundConstant_lt_cubic : cubicBoundConstant < (cubicPowerConstant : ℝ) := by
  have hh := Nat.le_ceil cubicBoundConstant
  simp only [cubicPowerConstant, Nat.cast_add, Nat.cast_one]
  linarith

/-- Every interval of this cubic length contains a coprime integer. -/
theorem isJacobsthalBound_cubic (k : ℕ) :
    IsJacobsthalBound k (cubicPowerConstant * (k + 1) ^ 3) := by
  classical
  by_contra hbad
  obtain ⟨P, hP, hcard, r, hcover⟩ :=
    (not_isJacobsthalBound_iff_cover k (cubicPowerConstant * (k + 1) ^ 3)).mp hbad
  have hm : cubicBoundConstant * ((k : ℝ) + 1) ^ 3 <
      (cubicPowerConstant * (k + 1) ^ 3 : ℕ) := by
    push_cast
    exact mul_lt_mul_of_pos_right cubicBoundConstant_lt_cubic (by positivity)
  obtain ⟨j, hj, havoid⟩ := prime_survivor_cubic P hP k hcard r _ hm
  obtain ⟨p, hp, hjp⟩ := hcover j hj
  exact havoid p hp hjp

theorem jacobsthalFunction_le_cubic (k : ℕ) :
    jacobsthalFunction k ≤ cubicPowerConstant * (k + 1) ^ 3 :=
  (jacobsthalFunction_le_iff k _).mpr (isJacobsthalBound_cubic k)

/-- The asymptotic conclusion has exponent three, not exponent two. -/
theorem exists_cubic_power_bound :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤ C * k ^ 3 := by
  have hD : (0 : ℝ) < cubicPowerConstant := by exact_mod_cast cubicPowerConstant_pos
  refine ⟨8 * (cubicPowerConstant : ℝ), by positivity, ?_⟩
  intro k hk
  have hkp : k + 1 ≤ 2 * k := by omega
  have hh := (jacobsthalFunction_le_cubic k).trans
    (Nat.mul_le_mul_left cubicPowerConstant (Nat.pow_le_pow_left hkp 3))
  have he : cubicPowerConstant * (2 * k) ^ 3 = (8 * cubicPowerConstant) * k ^ 3 := by ring
  rw [he] at hh
  exact_mod_cast hh

#print axioms isJacobsthalBound_cubic
#print axioms jacobsthalFunction_le_cubic
#print axioms exists_cubic_power_bound
end Erdos970
