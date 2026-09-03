import Submission.SelbergSoftPrimeBound

/-! A uniform sixth-power Jacobsthal bound. This strengthens the earlier
fixed-power bound but is not the conjectured quadratic theorem. -/
namespace Erdos970
open FiniteSelberg

noncomputable def sixthPowerConstant : ℕ := ⌈softBoundConstant⌉₊ + 1

lemma sixthPowerConstant_pos : 0 < sixthPowerConstant := Nat.succ_pos _

lemma softBoundConstant_lt_sixth : softBoundConstant < (sixthPowerConstant : ℝ) := by
  have hh := Nat.le_ceil softBoundConstant
  simp only [sixthPowerConstant, Nat.cast_add, Nat.cast_one]
  linarith

/-- Every interval of this sixth-power length contains a coprime integer. -/
theorem isJacobsthalBound_sixth (k : ℕ) :
    IsJacobsthalBound k (sixthPowerConstant * (k + 1) ^ 6) := by
  classical
  by_contra hbad
  obtain ⟨P, hP, hcard, r, hcover⟩ :=
    (not_isJacobsthalBound_iff_cover k (sixthPowerConstant * (k + 1) ^ 6)).mp hbad
  have hsize : Fintype.card P ≤ k := by simpa using hcard
  have hm : softBoundConstant * ((k : ℝ) + 1) ^ 6 <
      (sixthPowerConstant * (k + 1) ^ 6 : ℕ) := by
    push_cast
    exact mul_lt_mul_of_pos_right softBoundConstant_lt_sixth (by positivity)
  obtain ⟨j, hj, havoid⟩ := prime_survivor_soft (fun p : P => p.val)
    (fun p => hP p.val p.property) Subtype.val_injective k hsize r _ hm
  obtain ⟨p, hp, hjp⟩ := hcover j hj
  exact havoid ⟨p, hp⟩ hjp

theorem jacobsthalFunction_le_sixth (k : ℕ) :
    jacobsthalFunction k ≤ sixthPowerConstant * (k + 1) ^ 6 :=
  (jacobsthalFunction_le_iff k _).mpr (isJacobsthalBound_sixth k)

/-- The asymptotic conclusion has exponent six, not exponent two. -/
theorem exists_sixth_power_bound :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤ C * k ^ 6 := by
  have hD : (0 : ℝ) < sixthPowerConstant := by exact_mod_cast sixthPowerConstant_pos
  refine ⟨64 * (sixthPowerConstant : ℝ), by positivity, ?_⟩
  intro k hk
  have hkp : k + 1 ≤ 2 * k := by omega
  have hh := (jacobsthalFunction_le_sixth k).trans
    (Nat.mul_le_mul_left sixthPowerConstant (Nat.pow_le_pow_left hkp 6))
  have he : sixthPowerConstant * (2 * k) ^ 6 = (64 * sixthPowerConstant) * k ^ 6 := by ring
  rw [he] at hh
  exact_mod_cast hh

lemma sixthPowerConstant_le : sixthPowerConstant ≤ 2 ^ 50 := by
  have he : Real.exp (4 : ℝ) ≤ 81 := by
    have hh := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 4
    rw [← Real.exp_nat_mul] at hh
    norm_num at hh ⊢
    exact hh
  have hb : softBoundConstant ≤ ((2 ^ 49 : ℕ) : ℝ) := by
    unfold softBoundConstant
    norm_num at *
    nlinarith only [he]
  have hc : ⌈softBoundConstant⌉₊ ≤ 2 ^ 49 := Nat.ceil_le.mpr hb
  unfold sixthPowerConstant
  omega

/-- A fully explicit, deliberately loose numerical form of the bound. -/
theorem jacobsthalFunction_le_explicit_sixth (k : ℕ) :
    jacobsthalFunction k ≤ 2 ^ 50 * (k + 1) ^ 6 :=
  (jacobsthalFunction_le_sixth k).trans
    (Nat.mul_le_mul_right _ sixthPowerConstant_le)

#print axioms jacobsthalFunction_le_explicit_sixth
#print axioms isJacobsthalBound_sixth
#print axioms jacobsthalFunction_le_sixth
#print axioms exists_sixth_power_bound
end Erdos970
