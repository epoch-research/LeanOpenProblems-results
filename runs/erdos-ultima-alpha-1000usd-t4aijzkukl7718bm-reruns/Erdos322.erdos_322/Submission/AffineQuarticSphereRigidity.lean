import Submission.EuclideanQuadraticFactor

/-! Affine linear maps from a real two-sphere to a four-coordinate fourth-power
sphere are constant. -/
namespace Erdos322Research.AffineQuarticSphereRigidity
noncomputable section
open Finset Matrix
open scoped Classical
set_option Elab.async false
set_option maxHeartbeats 0

private theorem even_part (a : Fin 4 → ℝ) (v : Fin 4 → Fin 3 → ℝ) (C : ℝ)
    (h : ∀ x : Fin 3 → ℝ, x ⬝ᵥ x = 1 → ∑ i, (a i+v i ⬝ᵥ x)^4=C)
    (x : Fin 3 → ℝ) (hx : x ⬝ᵥ x=1) :
    ∑ i, (v i ⬝ᵥ x)^4 = C-∑ i, a i^4-6*∑ i, a i^2*(v i ⬝ᵥ x)^2 := by
  have hp := h x hx
  have hm := h (-x) (by simpa only [neg_dotProduct, dotProduct_neg, neg_neg] using hx)
  simp only [dotProduct_neg, Fin.sum_univ_four] at hp hm ⊢
  linear_combination (hp+hm)/2

private theorem homogeneous_even_part (a : Fin 4 → ℝ) (v : Fin 4 → Fin 3 → ℝ) (C : ℝ)
    (h : ∀ x : Fin 3 → ℝ, x ⬝ᵥ x=1 → ∑ i, (a i+v i ⬝ᵥ x)^4=C)
    (x : Fin 3 → ℝ) :
    ∑ i, (v i ⬝ᵥ x)^4 = (x ⬝ᵥ x)*
      ((C-∑ i, a i^4)*(x ⬝ᵥ x)-6*∑ i, a i^2*(v i ⬝ᵥ x)^2) := by
  by_cases hx : x=0
  · subst x
    simp
  have hnorm : 0<x ⬝ᵥ x := by
    apply lt_of_le_of_ne (by simp only [dotProduct]; exact sum_nonneg (fun _ _ ↦ mul_self_nonneg _))
    exact Ne.symm (dotProduct_self_eq_zero.not.mpr hx)
  let r := Real.sqrt (x ⬝ᵥ x)
  have hr : r≠0 := (Real.sqrt_pos.mpr hnorm).ne'
  have hsq : r^2=x ⬝ᵥ x := Real.sq_sqrt hnorm.le
  have hu : (r⁻¹ • x) ⬝ᵥ (r⁻¹ • x)=1 := by
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [← hsq]
    field_simp
  have he := even_part a v C h (r⁻¹ • x) hu
  simp only [dotProduct_smul, smul_eq_mul] at he
  have he' : ∑ i, (v i ⬝ᵥ x)^4 = (C-∑ i, a i^4)*r^4-
      6*r^2*∑ i, a i^2*(v i ⬝ᵥ x)^2 := by
    convert congrArg (fun z : ℝ ↦ r^4*z) he using 1 <;>
      simp only [Fin.sum_univ_four] <;> field_simp
  rw [show r^4=(r^2)^2 by ring, hsq] at he'
  linear_combination he'

/-- There is no nonconstant affine-linear map from the real two-sphere into
any fixed four-coordinate fourth-power sphere. -/
theorem linear_part_zero (a : Fin 4 → ℝ) (v : Fin 4 → Fin 3 → ℝ) (C : ℝ)
    (h : ∀ x : Fin 3 → ℝ, x ⬝ᵥ x=1 → ∑ i, (a i+v i ⬝ᵥ x)^4=C) : v=0 := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := fun j k ↦
    (C-∑ i, a i^4)*(1 : Matrix (Fin 3) (Fin 3) ℝ) j k -
      6*∑ i, a i^2*v i j*v i k
  apply PositiveQuadraticFactor.euclidean_factor_is_zero' v A
  intro x
  rw [homogeneous_even_part a v C h]
  congr 1
  simp only [dotProduct, mulVec, Fin.sum_univ_three]
  dsimp [A]
  simp only [Matrix.one_apply, Fin.sum_univ_four]
  norm_num [Fin.ext_iff]
  ring

end
end Erdos322Research.AffineQuarticSphereRigidity
