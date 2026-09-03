import Submission.PositiveQuadraticFactorObstruction

/-! The spectral extension of the four-linear-form factor obstruction. -/
namespace Erdos322Research.PositiveQuadraticFactor
noncomputable section
open Finset Matrix
open scoped Classical
set_option Elab.async false
set_option maxHeartbeats 0

private theorem norm_preserved (U : Matrix.unitaryGroup (Fin 3) ℝ) (x y : Fin 3 → ℝ) :
    ((U : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x) ⬝ᵥ ((U : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ y) = x ⬝ᵥ y := by
  have hU : (U : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * (U : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_star_mul_self U
  rw [dotProduct_mulVec, ← vecMul_transpose (U : Matrix (Fin 3) (Fin 3) ℝ) x,
    vecMul_vecMul, hU, vecMul_one]

private theorem factor_eval (U A : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    (U *ᵥ x) ⬝ᵥ (A *ᵥ (U *ᵥ x)) = x ⬝ᵥ ((Uᵀ*A*U) *ᵥ x) := by
  calc
    _ = (x ᵥ* Uᵀ) ⬝ᵥ (A *ᵥ (U *ᵥ x)) := by rw [vecMul_transpose]
    _ = x ⬝ᵥ (Uᵀ *ᵥ (A *ᵥ (U *ᵥ x))) := (dotProduct_mulVec x _ _).symm
    _ = _ := by rw [mulVec_mulVec, mulVec_mulVec]

/-- If a sum of four fourth powers of ternary real linear forms has the
Euclidean quadratic norm as a factor, then all four forms vanish. -/
theorem euclidean_factor_is_zero (v : Fin 4 → Fin 3 → ℝ)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.IsHermitian)
    (h : ∀ x : Fin 3 → ℝ, ∑ i, (v i ⬝ᵥ x)^4 = (x ⬝ᵥ x)*(x ⬝ᵥ (A *ᵥ x))) :
    v=0 := by
  let U := hA.eigenvectorUnitary
  have hdiag : (U : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * A * (U : Matrix (Fin 3) (Fin 3) ℝ) = diagonal hA.eigenvalues := by
    simpa only [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def]
      using hA.conjStarAlgAut_star_eigenvectorUnitary
  let w : Fin 4 → Fin 3 → ℝ := fun i ↦ v i ᵥ* (U : Matrix (Fin 3) (Fin 3) ℝ)
  have hw : w=0 := by
    apply diagonal_factor_is_zero w (hA.eigenvalues 0) (hA.eigenvalues 1) (hA.eigenvalues 2)
    intro x
    have hx := h ((U : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x)
    simp_rw [dotProduct_mulVec (v _)] at hx
    rw [norm_preserved, factor_eval, hdiag] at hx
    convert hx using 1
    simp only [dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_three]
    ring
  have hU : (U : Matrix (Fin 3) (Fin 3) ℝ) * (U : Matrix (Fin 3) (Fin 3) ℝ)ᵀ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_mul_star_self U
  funext i
  have hh := congrArg (fun z : Fin 3 → ℝ ↦ z ᵥ* (U : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) (congrFun hw i)
  change (v i ᵥ* (U : Matrix (Fin 3) (Fin 3) ℝ)) ᵥ* (U : Matrix (Fin 3) (Fin 3) ℝ)ᵀ =
    0 ᵥ* (U : Matrix (Fin 3) (Fin 3) ℝ)ᵀ at hh
  simpa only [vecMul_vecMul, hU, vecMul_one, zero_vecMul] using hh

/-- Symmetrizing the auxiliary quadratic factor removes the matrix-symmetry
hypothesis from the preceding result. -/
theorem euclidean_factor_is_zero' (v : Fin 4 → Fin 3 → ℝ)
    (A : Matrix (Fin 3) (Fin 3) ℝ)
    (h : ∀ x : Fin 3 → ℝ, ∑ i, (v i ⬝ᵥ x)^4 = (x ⬝ᵥ x)*(x ⬝ᵥ (A *ᵥ x))) :
    v=0 := by
  let B : Matrix (Fin 3) (Fin 3) ℝ := fun i j ↦ (A i j+A j i)/2
  have hB : B.IsHermitian := by
    ext i j
    simp only [conjTranspose_apply, star_trivial]
    dsimp [B]
    ring
  apply euclidean_factor_is_zero v B hB
  intro x
  rw [h]
  congr 1
  simp only [dotProduct, mulVec, Fin.sum_univ_three]
  dsimp [B]
  ring

end
end Erdos322Research.PositiveQuadraticFactor
