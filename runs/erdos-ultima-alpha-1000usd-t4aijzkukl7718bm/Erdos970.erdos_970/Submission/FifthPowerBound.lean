import Submission.SelbergSoftFifthBound

/-! A uniform fifth-power Jacobsthal bound. This strengthens the earlier
fixed-power bound but is not the conjectured quadratic theorem. -/
namespace Erdos970
open FiniteSelberg

noncomputable def fifthPowerConstant : ℕ := ⌈fifthBoundConstant⌉₊ + 1

lemma fifthPowerConstant_pos : 0 < fifthPowerConstant := Nat.succ_pos _

lemma fifthBoundConstant_lt_fifth : fifthBoundConstant < (fifthPowerConstant : ℝ) := by
  have hh := Nat.le_ceil fifthBoundConstant
  simp only [fifthPowerConstant, Nat.cast_add, Nat.cast_one]
  linarith

/-- Every interval of this fifth-power length contains a coprime integer. -/
theorem isJacobsthalBound_fifth (k : ℕ) :
    IsJacobsthalBound k (fifthPowerConstant * (k + 1) ^ 5) := by
  classical
  by_contra hbad
  obtain ⟨P, hP, hcard, r, hcover⟩ :=
    (not_isJacobsthalBound_iff_cover k (fifthPowerConstant * (k + 1) ^ 5)).mp hbad
  have hsize : Fintype.card P ≤ k := by simpa using hcard
  have hm : fifthBoundConstant * ((k : ℝ) + 1) ^ 5 <
      (fifthPowerConstant * (k + 1) ^ 5 : ℕ) := by
    push_cast
    exact mul_lt_mul_of_pos_right fifthBoundConstant_lt_fifth (by positivity)
  obtain ⟨j, hj, havoid⟩ := prime_survivor_soft_fifth (fun p : P => p.val)
    (fun p => hP p.val p.property) Subtype.val_injective k hsize r _ hm
  obtain ⟨p, hp, hjp⟩ := hcover j hj
  exact havoid ⟨p, hp⟩ hjp

theorem jacobsthalFunction_le_fifth (k : ℕ) :
    jacobsthalFunction k ≤ fifthPowerConstant * (k + 1) ^ 5 :=
  (jacobsthalFunction_le_iff k _).mpr (isJacobsthalBound_fifth k)

/-- The asymptotic conclusion has exponent five, not exponent two. -/
theorem exists_fifth_power_bound :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤ C * k ^ 5 := by
  have hD : (0 : ℝ) < fifthPowerConstant := by exact_mod_cast fifthPowerConstant_pos
  refine ⟨32 * (fifthPowerConstant : ℝ), by positivity, ?_⟩
  intro k hk
  have hkp : k + 1 ≤ 2 * k := by omega
  have hh := (jacobsthalFunction_le_fifth k).trans
    (Nat.mul_le_mul_left fifthPowerConstant (Nat.pow_le_pow_left hkp 5))
  have he : fifthPowerConstant * (2 * k) ^ 5 = (32 * fifthPowerConstant) * k ^ 5 := by ring
  rw [he] at hh
  exact_mod_cast hh

#print axioms isJacobsthalBound_fifth
#print axioms jacobsthalFunction_le_fifth
#print axioms exists_fifth_power_bound
end Erdos970
