import Submission.KernelProjectionEstimates

/-! An orthonormal basis adapted to the kernel of a nonzero real functional.
The first vector is the normalized Riesz representative; all remaining vectors
come from an arbitrary orthonormal basis of the kernel. -/
namespace Erdos3NormalOrthonormalBasis
open Finset Module
open scoped BigOperators RealInnerProductSpace Classical
set_option maxHeartbeats 3000000

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def unitNormal (F : E →L[ℝ] ℝ) : E :=
  ‖F‖⁻¹ • (InnerProductSpace.toDual ℝ E).symm F

lemma unitNormal_norm (F : E →L[ℝ] ℝ) (hF : F ≠ 0) : ‖unitNormal F‖ = 1 := by
  rw [unitNormal,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    (InnerProductSpace.toDual ℝ E).symm.norm_map,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hF)]

lemma unitNormal_inner (F : E →L[ℝ] ℝ) (x : E) : ⟪unitNormal F,x⟫ = F x/‖F‖ := by
  rw [unitNormal,real_inner_smul_left,InnerProductSpace.toDual_symm_apply]
  ring

lemma unitNormal_evaluate (F : E →L[ℝ] ℝ) (hF : F ≠ 0) : F (unitNormal F) = ‖F‖ := by
  have hh := unitNormal_inner F (unitNormal F)
  rw [real_inner_self_eq_norm_sq,unitNormal_norm F hF,one_pow] at hh
  have he := (eq_div_iff (norm_ne_zero_iff.mpr hF)).mp hh
  simpa only [one_mul] using he.symm

noncomputable def normalFamily (F : E →L[ℝ] ℝ) (o : OrthonormalBasis I ℝ F.toLinearMap.ker) :
    Unit ⊕ I → E := Sum.elim (fun _ ↦ unitNormal F) (fun i ↦ (o i : E))

lemma normalFamily_orthonormal (F : E →L[ℝ] ℝ) (hF : F ≠ 0)
    (o : OrthonormalBasis I ℝ F.toLinearMap.ker) : Orthonormal ℝ (normalFamily F o) := by
  apply orthonormal_iff_ite.mpr
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j => simp [normalFamily,real_inner_self_eq_norm_sq,unitNormal_norm F hF]
    | inr j =>
      have hz : F (o j : E) = 0 := (o j).property
      simp only [normalFamily,Sum.elim_inl,Sum.elim_inr,unitNormal_inner,hz,zero_div,
        Sum.inl_ne_inr,if_false]
  | inr i =>
    cases j with
    | inl j =>
      have hz : F (o i : E) = 0 := (o i).property
      rw [real_inner_comm]
      simp only [normalFamily,Sum.elim_inl,Sum.elim_inr,unitNormal_inner,hz,zero_div,
        Sum.inr_ne_inl,if_false]
    | inr j =>
      simpa only [normalFamily,Sum.elim_inr,Sum.inr.injEq] using o.inner_eq_ite i j

lemma normalFamily_span (F : E →L[ℝ] ℝ) (hF : F ≠ 0)
    (o : OrthonormalBasis I ℝ F.toLinearMap.ker) :
    ⊤ ≤ Submodule.span ℝ (Set.range (normalFamily F o)) := by
  intro x _
  let p := x-(F x/‖F‖) • unitNormal F
  have hp : F p = 0 := by
    dsimp only [p]
    rw [map_sub,map_smul,unitNormal_evaluate F hF,smul_eq_mul,
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hF),sub_self]
  let pK : F.toLinearMap.ker := ⟨p,hp⟩
  have hnormal : unitNormal F ∈ Submodule.span ℝ (Set.range (normalFamily F o)) :=
    Submodule.subset_span ⟨Sum.inl Unit.unit,rfl⟩
  have ho (i : I) : (o i : E) ∈ Submodule.span ℝ (Set.range (normalFamily F o)) :=
    Submodule.subset_span ⟨Sum.inr i,rfl⟩
  have hpmem : p ∈ Submodule.span ℝ (Set.range (normalFamily F o)) := by
    have he : (∑ i, (o.toBasis.repr pK i) • (o i : E)) = p := by
      have hh := congrArg (fun y : F.toLinearMap.ker ↦ (y : E)) (o.toBasis.sum_repr pK)
      simpa only [Submodule.coe_sum,Submodule.coe_smul,OrthonormalBasis.coe_toBasis] using hh
    rw [← he]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (ho i)
  have he : x = (F x/‖F‖) • unitNormal F+p := by dsimp only [p]; abel
  rw [he]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hnormal) hpmem

noncomputable def splitOrthonormalBasis (F : E →L[ℝ] ℝ) (hF : F ≠ 0)
    (o : OrthonormalBasis I ℝ F.toLinearMap.ker) : OrthonormalBasis (Unit ⊕ I) ℝ E :=
  OrthonormalBasis.mk (normalFamily_orthonormal F hF o) (normalFamily_span F hF o)

lemma splitOrthonormalBasis_left (F : E →L[ℝ] ℝ) (hF : F ≠ 0)
    (o : OrthonormalBasis I ℝ F.toLinearMap.ker) (i : Unit) :
    splitOrthonormalBasis F hF o (Sum.inl i) = unitNormal F := by
  simp [splitOrthonormalBasis,normalFamily]

lemma splitOrthonormalBasis_right (F : E →L[ℝ] ℝ) (hF : F ≠ 0)
    (o : OrthonormalBasis I ℝ F.toLinearMap.ker) (i : I) :
    splitOrthonormalBasis F hF o (Sum.inr i) = (o i : E) := by
  simp [splitOrthonormalBasis,normalFamily]

#print axioms splitOrthonormalBasis
end Erdos3NormalOrthonormalBasis
