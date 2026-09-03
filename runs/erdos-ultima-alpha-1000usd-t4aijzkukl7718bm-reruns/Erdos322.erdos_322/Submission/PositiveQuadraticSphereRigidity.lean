import Submission.RealQuadraticSphereFour

/-! Quadratic maps from arbitrary positive definite real quadratic norms to
four-coordinate fourth-power spheres are radial, in source dimension three or four. -/
namespace Erdos322Research.RealQuadraticSphereRigidity
noncomputable section
open Finset Matrix
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
set_option Elab.async false
set_option maxHeartbeats 0

private theorem change_eval {n : Type*} [Fintype n]
    (U A : Matrix n n ℝ) (x : n → ℝ) :
    (U *ᵥ x) ⬝ᵥ (A *ᵥ (U *ᵥ x)) = x ⬝ᵥ ((Uᵀ*A*U) *ᵥ x) := by
  calc
    _ = (x ᵥ* Uᵀ) ⬝ᵥ (A *ᵥ (U *ᵥ x)) := by rw [vecMul_transpose]
    _ = x ⬝ᵥ (Uᵀ *ᵥ (A *ᵥ (U *ᵥ x))) := (dotProduct_mulVec x _ _).symm
    _ = _ := by rw [mulVec_mulVec, mulVec_mulVec]

private theorem positive_source {n : Type*} [Fintype n] [DecidableEq n]
    (H : ∀ (A : Fin 4 → Matrix n n ℝ) (C : ℝ),
      (∀ x : n → ℝ, ∑ i, (x ⬝ᵥ (A i *ᵥ x))^4=C*(x ⬝ᵥ x)^4) →
      ∃ r : Fin 4 → ℝ, ∀ i x, x ⬝ᵥ (A i *ᵥ x)=r i*(x ⬝ᵥ x))
    (A : Fin 4 → Matrix n n ℝ) (G : Matrix n n ℝ) (hG : G.PosDef) (C : ℝ)
    (h : ∀ x : n → ℝ, ∑ i, (x ⬝ᵥ (A i *ᵥ x))^4=C*(x ⬝ᵥ (G *ᵥ x))^4) :
    ∃ r : Fin 4 → ℝ, ∀ i x, x ⬝ᵥ (A i *ᵥ x)=r i*(x ⬝ᵥ (G *ᵥ x)) := by
  obtain ⟨B,hB,hGB⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hG.isStrictlyPositive
  obtain ⟨b,rfl⟩ := hB
  have hGB' : G=(b : Matrix n n ℝ)ᵀ*(b : Matrix n n ℝ) := by
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using hGB
  let T : Matrix n n ℝ := ↑b⁻¹
  have hBT : (b : Matrix n n ℝ)*T=1 := b.val_inv
  have hTB : T*(b : Matrix n n ℝ)=1 := b.inv_val
  have hn (x : n → ℝ) : x ⬝ᵥ (G *ᵥ x)=((b : Matrix n n ℝ)*ᵥ x) ⬝ᵥ ((b : Matrix n n ℝ)*ᵥ x) := by
    rw [hGB',← mulVec_mulVec,dotProduct_mulVec,vecMul_transpose]
  have hnT (x : n → ℝ) : (T *ᵥ x) ⬝ᵥ (G *ᵥ (T *ᵥ x))=x ⬝ᵥ x := by
    rw [hn,mulVec_mulVec,hBT,one_mulVec]
  obtain ⟨r,hr⟩ := H (fun i ↦ Tᵀ*A i*T) C (by
    intro x
    have hh := h (T *ᵥ x)
    simp_rw [change_eval T (A _)] at hh
    rwa [hnT] at hh)
  refine ⟨r,?_⟩
  intro i x
  have he := change_eval T (A i) ((b : Matrix n n ℝ)*ᵥ x)
  rw [mulVec_mulVec,hTB,one_mulVec] at he
  calc
    x ⬝ᵥ (A i *ᵥ x) = ((b : Matrix n n ℝ)*ᵥ x) ⬝ᵥ ((Tᵀ*A i*T) *ᵥ ((b : Matrix n n ℝ)*ᵥ x)) := he
    _ = r i*(((b : Matrix n n ℝ)*ᵥ x) ⬝ᵥ ((b : Matrix n n ℝ)*ᵥ x)) := hr i _
    _ = r i*(x ⬝ᵥ (G *ᵥ x)) := by rw [hn]

/-- Real quadratic maps based on any positive definite ternary source norm
cannot give distinct points on a fixed fourth-power sphere. -/
theorem radial_positive_ternary (A : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ)
    (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.PosDef) (C : ℝ)
    (h : ∀ x : Fin 3 → ℝ, ∑ i, (x ⬝ᵥ (A i *ᵥ x))^4=C*(x ⬝ᵥ (G *ᵥ x))^4) :
    ∃ r : Fin 4 → ℝ, ∀ i x, x ⬝ᵥ (A i *ᵥ x)=r i*(x ⬝ᵥ (G *ᵥ x)) :=
  positive_source radial_ternary A G hG C h

/-- In particular, arbitrary weighted quaternion-type source norms do not
avoid quadratic-map rigidity. All coefficients may be real. -/
theorem radial_positive_four (A : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ)
    (G : Matrix (Fin 4) (Fin 4) ℝ) (hG : G.PosDef) (C : ℝ)
    (h : ∀ x : Fin 4 → ℝ, ∑ i, (x ⬝ᵥ (A i *ᵥ x))^4=C*(x ⬝ᵥ (G *ᵥ x))^4) :
    ∃ r : Fin 4 → ℝ, ∀ i x, x ⬝ᵥ (A i *ᵥ x)=r i*(x ⬝ᵥ (G *ᵥ x)) :=
  positive_source radial_four A G hG C h

/-- Equal values of the source norm give identical output tuples, rather than
merely identical fourth-power norms. -/
theorem constant_on_positive_four_fibers (A : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ)
    (G : Matrix (Fin 4) (Fin 4) ℝ) (hG : G.PosDef) (C : ℝ)
    (h : ∀ x : Fin 4 → ℝ, ∑ i, (x ⬝ᵥ (A i *ᵥ x))^4=C*(x ⬝ᵥ (G *ᵥ x))^4)
    (x y : Fin 4 → ℝ) (hxy : x ⬝ᵥ (G *ᵥ x)=y ⬝ᵥ (G *ᵥ y)) :
    ∀ i, x ⬝ᵥ (A i *ᵥ x)=y ⬝ᵥ (A i *ᵥ y) := by
  obtain ⟨r,hr⟩ := radial_positive_four A G hG C h
  intro i
  rw [hr,hr,hxy]

end
end Erdos322Research.RealQuadraticSphereRigidity
