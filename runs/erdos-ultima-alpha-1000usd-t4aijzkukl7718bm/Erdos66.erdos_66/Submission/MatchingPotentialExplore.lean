import Submission.MatchingPacketSelectionExplore
import Submission.JointRepairPotentialExplore

/-! Summable joint self/mixed packet potentials, with thresholds uniform in
the finite coordinate prefix. -/
namespace Erdos66MatchingPotential
open Filter Erdos66JointRepairPotential Erdos66ClippedRepair
open scoped Topology Classical
set_option maxHeartbeats 1200000

noncomputable def combined (B Q ε : ℝ) (z : ℕ) : ℝ :=
  potential B ε z + Real.exp (((Real.exp (8*(4/ε))-1)*4*Q^2)-4*logScale z)

lemma combined_pos (B Q ε : ℝ) (z : ℕ) : 0 < combined B Q ε z :=
  add_pos (potential_pos B ε z) (Real.exp_pos _)

lemma combined_summable (B Q ε : ℝ) : Summable (combined B Q ε) := by
  have he : (fun z ↦ Real.exp (((Real.exp (8*(4/ε))-1)*4*Q^2)-4*logScale z)) =
      fun z ↦ Real.exp ((Real.exp (8*(4/ε))-1)*4*Q^2)*potential 0 ε z := by
    funext z
    simp only [potential,mul_zero,zero_mul,zero_sub,← Real.exp_add]
    congr 1
  exact (potential_summable B ε).add ((potential_summable 0 ε).mul_left _ |>.congr (fun z ↦ congrFun he.symm z))

lemma combined_bound (B Q ε H M : ℝ) (hε : 0 < ε) (hM : 0 ≤ M) (hMQ : M ≤ Q)
    (z : ℕ) (hH : H ≤ B*Real.sqrt (logScale z)) :
    Real.exp (Real.exp (4/ε)*H-(4/ε)*(ε*logScale z))+
      Real.exp ((Real.exp (8*(4/ε))-1)*4*M^2-(4/ε)*(ε*logScale z)) ≤ combined B Q ε z := by
  have hfirst := hit_potential_le B ε H hε z hH
  have he : (4/ε)*(ε*logScale z) = 4*logScale z := by field_simp
  apply add_le_add hfirst
  rw [he]
  apply Real.exp_le_exp.mpr
  have hq : M^2 ≤ Q^2 := sq_le_sq₀ hM (hM.trans hMQ) |>.mpr hMQ
  have hcoef : 0 ≤ (Real.exp (8*(4/ε))-1)*4 := by
    have hh := Real.one_le_exp (show 0 ≤ 8*(4/ε) by positivity)
    exact mul_nonneg (sub_nonneg.mpr hh) (by norm_num)
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left hq hcoef) _

lemma exists_combined_tail (B Q ε δ : ℝ) (hδ : 0 < δ) :
    ∃ Z : ℕ, ∀ T : Finset ℕ, (∀ z ∈ T, Z ≤ z) → ∑ z ∈ T, combined B Q ε z < δ := by
  obtain ⟨Z,hZ⟩ := ((tendsto_sum_nat_add (combined B Q ε)).eventually_lt_const hδ).exists
  refine ⟨Z,fun T hT ↦ ?_⟩
  let U := T.image (fun z ↦ z-Z)
  have hinj : Set.InjOn (fun z ↦ z-Z) (T : Set ℕ) := by
    intro a ha b hb he
    have ha' := hT a ha
    have hb' := hT b hb
    dsimp only at he
    omega
  have he : (∑ z ∈ T, combined B Q ε z) = ∑ u ∈ U, combined B Q ε (u+Z) := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro z hz
      rw [Nat.sub_add_cancel (hT z hz)]
    · exact hinj
  rw [he]
  have hs := (summable_nat_add_iff Z).mpr (combined_summable B Q ε)
  exact (hs.sum_le_tsum U (fun u _ ↦ (combined_pos B Q ε (u+Z)).le)).trans_lt hZ

end Erdos66MatchingPotential
