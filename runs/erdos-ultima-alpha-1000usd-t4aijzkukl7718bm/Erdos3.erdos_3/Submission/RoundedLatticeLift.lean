import Submission.KernelShearLattice

/-! Rounding a lift modulo a shortest lattice vector. A triangle inequality
suffices for a factor-two bound; orthogonality is not needed for this step. -/
namespace Erdos3RoundedLatticeLift
open Module Erdos3KernelProjectionEstimates Erdos3KernelShearLattice
open scoped Classical
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def roundedLift (G : E →L[ℝ] ℝ) (v x : E) : E :=
  x - round (G x) • v

lemma roundedLift_mem (L : Submodule ℤ E) (G : E →L[ℝ] ℝ) (v x : E)
    (hv : v ∈ L) (hx : x ∈ L) : roundedLift G v x ∈ L :=
  L.sub_mem hx (L.smul_mem _ hv)

lemma roundedLift_projection (G : E →L[ℝ] ℝ) (v x : E) (hv : G v = 1) :
    projectionAlong G v (roundedLift G v x) = projectionAlong G v x := by
  have hz : projectionAlong G v v = 0 := by simp [projectionAlong_apply,hv]
  simp only [roundedLift,map_sub,map_zsmul,hz,smul_zero,sub_zero]

lemma roundedLift_decomposition (G : E →L[ℝ] ℝ) (v x : E) :
    roundedLift G v x = projectionAlong G v x + (G x - (round (G x) : ℝ)) • v := by
  rw [roundedLift,projectionAlong_apply,sub_smul,Int.cast_smul_eq_zsmul ℝ]
  abel

lemma roundedLift_norm (G : E →L[ℝ] ℝ) (v x : E) :
    ‖roundedLift G v x‖ ≤ ‖projectionAlong G v x‖ + ‖v‖/2 := by
  rw [roundedLift_decomposition]
  calc
    _ ≤ ‖projectionAlong G v x‖ + ‖(G x - (round (G x) : ℝ)) • v‖ := norm_add_le _ _
    _ = ‖projectionAlong G v x‖ + |G x - (round (G x) : ℝ)| * ‖v‖ := by
      rw [norm_smul,Real.norm_eq_abs]
    _ ≤ ‖projectionAlong G v x‖ + (1/2 : ℝ) * ‖v‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right (abs_sub_round _) (norm_nonneg _))
    _ = _ := by ring

/-- A nonzero projected vector has a lattice lift of at most twice its norm. -/
theorem shortest_roundedLift_norm (L : Submodule ℤ E) (G : E →L[ℝ] ℝ) (v x : E)
    (hvL : v ∈ L) (hv : G v = 1) (hx : x ∈ L)
    (hmin : ∀ y : E, y ∈ L → y ≠ 0 → ‖v‖ ≤ ‖y‖)
    (hp : projectionAlong G v x ≠ 0) :
    ‖roundedLift G v x‖ ≤ 2*‖projectionAlong G v x‖ ∧
      ‖v‖ ≤ 2*‖projectionAlong G v x‖ := by
  have hu0 : roundedLift G v x ≠ 0 := by
    intro hz
    apply hp
    rw [← roundedLift_projection G v x hv,hz,map_zero]
  have hm := hmin (roundedLift G v x) (roundedLift_mem L G v x hvL hx) hu0
  have hu := roundedLift_norm G v x
  constructor <;> linarith

#print axioms shortest_roundedLift_norm
end Erdos3RoundedLatticeLift
