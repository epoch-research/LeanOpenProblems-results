import FormalConjecturesUtil

/-! Explicit projection onto the kernel of a real functional. In a Hilbert
space the normal is chosen by Riesz representation, giving the exact norm
error |F x|/norm(F). -/
namespace Erdos3KernelProjectionEstimates
open scoped RealInnerProductSpace
set_option maxHeartbeats 2000000

section Normed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def projectionAlong (F : E →L[ℝ] ℝ) (u : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E-F.smulRight u

lemma projectionAlong_apply (F : E →L[ℝ] ℝ) (u x : E) :
    projectionAlong F u x = x-F x • u := rfl

lemma projectionAlong_mem_ker (F : E →L[ℝ] ℝ) (u : E) (hu : F u = 1) (x : E) :
    projectionAlong F u x ∈ F.toLinearMap.ker := by
  change F (x-F x • u) = 0
  rw [map_sub,map_smul,hu,smul_eq_mul,mul_one,sub_self]

lemma projectionAlong_eq_self (F : E →L[ℝ] ℝ) (u x : E) (hx : F x = 0) :
    projectionAlong F u x = x := by rw [projectionAlong_apply,hx,zero_smul,sub_zero]

lemma projectionAlong_error (F : E →L[ℝ] ℝ) (u x : E) :
    ‖x-projectionAlong F u x‖ = |F x| *‖u‖ := by
  rw [projectionAlong_apply,sub_sub_cancel,norm_smul,Real.norm_eq_abs]

noncomputable def projectToKernel (F : E →L[ℝ] ℝ) (u : E) (hu : F u = 1) :
    E →L[ℝ] F.toLinearMap.ker :=
  (projectionAlong F u).codRestrict F.toLinearMap.ker (projectionAlong_mem_ker F u hu)

end Normed

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def normalVector (F : E →L[ℝ] ℝ) : E :=
  (‖F‖^2)⁻¹ • (InnerProductSpace.toDual ℝ E).symm F

lemma normalVector_evaluate (F : E →L[ℝ] ℝ) (hF : F ≠ 0) : F (normalVector F) = 1 := by
  have hn := (InnerProductSpace.toDual ℝ E).symm.norm_map F
  have he : F ((InnerProductSpace.toDual ℝ E).symm F) = ‖F‖^2 := by
    rw [← InnerProductSpace.toDual_symm_apply,real_inner_self_eq_norm_sq,hn]
  rw [normalVector,map_smul,he,smul_eq_mul,inv_mul_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.mpr hF))]

lemma normalVector_norm (F : E →L[ℝ] ℝ) (hF : F ≠ 0) : ‖normalVector F‖ = 1/‖F‖ := by
  rw [normalVector,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _)),
    (InnerProductSpace.toDual ℝ E).symm.norm_map]
  have hn : ‖F‖ ≠ 0 := norm_ne_zero_iff.mpr hF
  field_simp

lemma normal_projection_error (F : E →L[ℝ] ℝ) (hF : F ≠ 0) (x : E) :
    ‖x-projectionAlong F (normalVector F) x‖ = |F x|/‖F‖ := by
  rw [projectionAlong_error,normalVector_norm F hF]
  ring

#print axioms normal_projection_error
end Hilbert
end Erdos3KernelProjectionEstimates
