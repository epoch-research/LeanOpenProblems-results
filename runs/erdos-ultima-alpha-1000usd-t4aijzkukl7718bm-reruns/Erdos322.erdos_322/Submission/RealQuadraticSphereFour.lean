import Submission.RealQuadraticSphereRigidity

/-! The real quadratic sphere-map obstruction in four input coordinates. -/
namespace Erdos322Research.RealQuadraticSphereRigidity
noncomputable section
open Finset Matrix
open scoped Classical
set_option Elab.async false
set_option maxHeartbeats 0

private def indices (j : Fin 3) : Fin 3 → Fin 4 :=
  if j=0 then ![0,1,2] else if j=1 then ![0,1,3] else ![0,2,3]

private def liftChart (j : Fin 3) (x : Fin 3 → ℝ) : Fin 4 → ℝ :=
  if j=0 then ![x 0,x 1,x 2,0] else if j=1 then ![x 0,x 1,0,x 2] else ![x 0,0,x 1,x 2]

private theorem chart_norm (j : Fin 3) (x : Fin 3 → ℝ) :
    liftChart j x ⬝ᵥ liftChart j x=x ⬝ᵥ x := by
  fin_cases j <;> simp only [dotProduct,Fin.sum_univ_three,Fin.sum_univ_four] <;>
    dsimp [liftChart] <;> ring

private theorem chart_eval (A : Matrix (Fin 4) (Fin 4) ℝ) (j : Fin 3) (x : Fin 3 → ℝ) :
    liftChart j x ⬝ᵥ (A *ᵥ liftChart j x)=
      x ⬝ᵥ ((A.submatrix (indices j) (indices j)) *ᵥ x) := by
  fin_cases j <;> simp only [dotProduct,mulVec,Fin.sum_univ_three,Fin.sum_univ_four] <;>
    dsimp [liftChart,Matrix.submatrix,indices] <;> ring

/-- Quadratic sphere-map rigidity over the reals with four source coordinates. -/
theorem radial_four (A : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ) (C : ℝ)
    (h : ∀ x : Fin 4 → ℝ, ∑ i, (x ⬝ᵥ (A i *ᵥ x))^4=C*(x ⬝ᵥ x)^4) :
    ∃ r : Fin 4 → ℝ, ∀ i x, x ⬝ᵥ (A i *ᵥ x)=r i*(x ⬝ᵥ x) := by
  have hc (j : Fin 3) : ∃ r : Fin 4 → ℝ, ∀ i x,
      x ⬝ᵥ ((A i).submatrix (indices j) (indices j) *ᵥ x)=r i*(x ⬝ᵥ x) := by
    apply radial_ternary _ C
    intro x
    have hh := h (liftChart j x)
    simp_rw [chart_eval] at hh
    rwa [chart_norm] at hh
  choose r hr using hc
  have hre (j : Fin 3) (i : Fin 4) : r j i=A i 0 0 := by
    have hh := hr j i ![1,0,0]
    simp only [dotProduct,mulVec,Fin.sum_univ_three] at hh
    fin_cases j <;> dsimp [indices,Matrix.submatrix] at hh ⊢ <;> linarith
  simp only [hre] at hr
  refine ⟨fun i ↦ A i 0 0,?_⟩
  intro i x
  have h012 := hr 0 i ![x 0,x 1,x 2]
  have h013 := hr 1 i ![x 0,x 1,x 3]
  have h023 := hr 2 i ![x 0,x 2,x 3]
  have h01 := hr 0 i ![x 0,x 1,0]
  have h02 := hr 0 i ![x 0,0,x 2]
  have h03 := hr 1 i ![x 0,0,x 3]
  have h0 := hr 0 i ![x 0,0,0]
  simp only [dotProduct,mulVec,Fin.sum_univ_three,Fin.sum_univ_four]
    at h012 h013 h023 h01 h02 h03 h0 ⊢
  dsimp [indices,Matrix.submatrix] at h012 h013 h023 h01 h02 h03 h0
  linear_combination h012+h013+h023-h01-h02-h03+h0

end
end Erdos322Research.RealQuadraticSphereRigidity
