import Submission.QuadraticSphereEqualAxes
import Submission.QuarticLevelTriple

/-! Real quadratic maps from ternary Euclidean spheres to four-coordinate
fourth-power spheres are radial. -/
namespace Erdos322Research.RealQuadraticSphereRigidity
noncomputable section
open Finset Matrix
open scoped Classical
set_option Elab.async false
set_option maxHeartbeats 0

private def kernelMatrix (q : Fin 5 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![q 0,q 2,q 3],![q 2,q 1,q 4],![q 3,q 4,-q 0-q 1]]

private theorem exists_kernel (A : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ) :
    ∃ S : Matrix (Fin 3) (Fin 3) ℝ,
      S.IsHermitian ∧ S≠0 ∧ trace S=0 ∧ ∀ i, trace (S*A i)=0 := by
  let L : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) :=
    { toFun := fun q i ↦ trace (kernelMatrix q*A i)
      map_add' := by
        intro q r
        funext i
        simp only [trace,Matrix.diag,Matrix.mul_apply,Fin.sum_univ_three]
        simp only [kernelMatrix,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
          Matrix.head_cons,Matrix.tail_cons,Pi.add_apply]
        ring
      map_smul' := by
        intro s q
        funext i
        simp only [trace,Matrix.diag,Matrix.mul_apply,Fin.sum_univ_three]
        simp only [kernelMatrix,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
          Matrix.head_cons,Matrix.tail_cons,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
        ring }
  have hk := LinearMap.ker_ne_bot_of_finrank_lt (f := L) (by norm_num)
  obtain ⟨q,hq,hqne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  refine ⟨kernelMatrix q,?_,?_,?_,?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro hz
    apply hqne
    funext j
    have h00 := congrFun (congrFun hz 0) 0
    have h11 := congrFun (congrFun hz 1) 1
    have h01 := congrFun (congrFun hz 0) 1
    have h02 := congrFun (congrFun hz 0) 2
    have h12 := congrFun (congrFun hz 1) 2
    fin_cases j <;> assumption
  · simp only [trace,Matrix.diag,Fin.sum_univ_three]
    simp only [kernelMatrix,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
          Matrix.head_cons,Matrix.tail_cons]
    ring
  · intro i
    exact congrFun hq i

private theorem orthogonal_dot (U : Matrix.unitaryGroup (Fin 3) ℝ) (x y : Fin 3 → ℝ) :
    ((U : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x) ⬝ᵥ ((U : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ y) = x ⬝ᵥ y := by
  have hU : (U : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * (U : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_star_mul_self U
  rw [dotProduct_mulVec, ← vecMul_transpose (U : Matrix (Fin 3) (Fin 3) ℝ) x,
    vecMul_vecMul, hU, vecMul_one]

private theorem orthogonal_eval (U A : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    (U *ᵥ x) ⬝ᵥ (A *ᵥ (U *ᵥ x)) = x ⬝ᵥ ((Uᵀ*A*U) *ᵥ x) := by
  calc
    _ = (x ᵥ* Uᵀ) ⬝ᵥ (A *ᵥ (U *ᵥ x)) := by rw [vecMul_transpose]
    _ = x ⬝ᵥ (Uᵀ *ᵥ (A *ᵥ (U *ᵥ x))) := (dotProduct_mulVec x _ _).symm
    _ = _ := by rw [mulVec_mulVec, mulVec_mulVec]

private theorem equal_axes_after_rotation (A : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ) (C : ℝ)
    (h : ∀ x : Fin 3 → ℝ, ∑ i, (x ⬝ᵥ (A i *ᵥ x))^4=C*(x ⬝ᵥ x)^4) :
    ∃ U : Matrix.unitaryGroup (Fin 3) ℝ,
      let B := fun i ↦ (U : Matrix (Fin 3) (Fin 3) ℝ)ᵀ*A i*(U : Matrix (Fin 3) (Fin 3) ℝ)
      (∀ i, B i 0 0=B i 1 1) ∨ (∀ i, B i 0 0=B i 2 2) ∨ (∀ i, B i 1 1=B i 2 2) := by
  obtain ⟨S,hS,hS0,htr,hSA⟩ := exists_kernel A
  let U := hS.eigenvectorUnitary
  let B := fun i ↦ (U : Matrix (Fin 3) (Fin 3) ℝ)ᵀ*A i*(U : Matrix (Fin 3) (Fin 3) ℝ)
  let lam := hS.eigenvalues
  have hdiag : S=(U : Matrix (Fin 3) (Fin 3) ℝ)*diagonal lam*(U : Matrix (Fin 3) (Fin 3) ℝ)ᵀ := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial,Function.comp_def] using hS.spectral_theorem
  have hn : lam 0≠0 ∨ lam 1≠0 ∨ lam 2≠0 := by
    by_contra hn
    push_neg at hn
    apply hS0
    apply hS.eigenvalues_eq_zero_iff.mp
    funext j
    fin_cases j <;> simp only [Pi.zero_apply] <;> tauto
  have hs : lam 0+lam 1+lam 2=0 := by
    have hh := hS.trace_eq_sum_eigenvalues
    rw [htr,Fin.sum_univ_three] at hh
    exact hh.symm
  have hr (i : Fin 4) : lam 0*B i 0 0+lam 1*B i 1 1+lam 2*B i 2 2=0 := by
    calc
      _ = trace (diagonal lam*B i) := by
        simp only [trace,Matrix.diag,diagonal_mul,Fin.sum_univ_three]
      _ = trace (S*A i) := by
        rw [hdiag]
        dsimp [B]
        calc
          _ = trace ((diagonal lam*((U : Matrix (Fin 3) (Fin 3) ℝ)ᵀ*A i))*(U : Matrix (Fin 3) (Fin 3) ℝ)) := by
            simp only [Matrix.mul_assoc]
          _ = trace ((U : Matrix (Fin 3) (Fin 3) ℝ)*(diagonal lam*((U : Matrix (Fin 3) (Fin 3) ℝ)ᵀ*A i))) := trace_mul_comm _ _
          _ = _ := by simp only [Matrix.mul_assoc]
      _ = 0 := hSA i
  have hu (j : Fin 3) : QuarticLevelTriple.fourthNorm (fun i ↦ B i j j)=C := by
    have hh := h ((U : Matrix (Fin 3) (Fin 3) ℝ)*ᵥ Pi.single j 1)
    simp_rw [orthogonal_eval] at hh
    rw [orthogonal_dot] at hh
    simpa only [single_one_dotProduct,mulVec_single_one,col_apply,Pi.single_eq_same,one_pow,mul_one]
      using hh
  have heq := QuarticLevelTriple.equal_pair (fun j i ↦ B i j j) C (lam 0) (lam 1) (lam 2) hu hn hs hr
  refine ⟨U,?_⟩
  rcases heq with heq|heq|heq
  · left; exact fun i ↦ congrFun heq i
  · right; left; exact fun i ↦ congrFun heq i
  · right; right; exact fun i ↦ congrFun heq i

private def coeff (A : Matrix (Fin 3) (Fin 3) ℝ) : Fin 6 → ℝ :=
  ![A 0 0,A 1 1,A 2 2,A 0 1+A 1 0,A 0 2+A 2 0,A 1 2+A 2 1]

private theorem quad_coeff (A : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    QuadraticSphereEqualAxes.quad (coeff A) x=x ⬝ᵥ (A *ᵥ x) := by
  simp only [QuadraticSphereEqualAxes.quad,dotProduct,mulVec,Fin.sum_univ_three]
  dsimp [coeff]
  ring

/-- Every real homogeneous quadratic map from ternary Euclidean spheres into
four-coordinate fourth-power spheres is radial. No rationality or symmetry
assumption is imposed on the coefficient matrices. -/
theorem radial_ternary (A : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ) (C : ℝ)
    (h : ∀ x : Fin 3 → ℝ, ∑ i, (x ⬝ᵥ (A i *ᵥ x))^4=C*(x ⬝ᵥ x)^4) :
    ∃ r : Fin 4 → ℝ, ∀ i x, x ⬝ᵥ (A i *ᵥ x)=r i*(x ⬝ᵥ x) := by
  obtain ⟨U,heq⟩ := equal_axes_after_rotation A C h
  let B := fun i ↦ (U : Matrix (Fin 3) (Fin 3) ℝ)ᵀ*A i*(U : Matrix (Fin 3) (Fin 3) ℝ)
  have h' (x : Fin 3 → ℝ) : ∑ i, QuadraticSphereEqualAxes.quad (coeff (B i)) x^4=C*(x ⬝ᵥ x)^4 := by
    simp only [quad_coeff]
    have hh := h ((U : Matrix (Fin 3) (Fin 3) ℝ)*ᵥ x)
    simp_rw [orthogonal_eval] at hh
    rw [orthogonal_dot] at hh
    exact hh
  have heq' : (∀ i, coeff (B i) 0=coeff (B i) 1) ∨
      (∀ i, coeff (B i) 0=coeff (B i) 2) ∨ (∀ i, coeff (B i) 1=coeff (B i) 2) := heq
  obtain ⟨r,hrad⟩ := QuadraticSphereEqualAxes.radial_of_some_equal_axes (fun i ↦ coeff (B i)) C h' heq'
  have hU : (U : Matrix (Fin 3) (Fin 3) ℝ)*(U : Matrix (Fin 3) (Fin 3) ℝ)ᵀ=1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_mul_star_self U
  refine ⟨r,?_⟩
  intro i x
  have hx : (U : Matrix (Fin 3) (Fin 3) ℝ)*ᵥ ((U : Matrix (Fin 3) (Fin 3) ℝ)ᵀ*ᵥ x)=x := by
    rw [mulVec_mulVec,hU,one_mulVec]
  have hh := hrad i ((U : Matrix (Fin 3) (Fin 3) ℝ)ᵀ*ᵥ x)
  rw [quad_coeff] at hh
  have he := orthogonal_eval (U : Matrix (Fin 3) (Fin 3) ℝ) (A i) ((U : Matrix (Fin 3) (Fin 3) ℝ)ᵀ*ᵥ x)
  rw [hx] at he
  have hn := orthogonal_dot U ((U : Matrix (Fin 3) (Fin 3) ℝ)ᵀ*ᵥ x) ((U : Matrix (Fin 3) (Fin 3) ℝ)ᵀ*ᵥ x)
  rw [hx] at hn
  rw [← he,← hn] at hh
  exact hh

end
end Erdos322Research.RealQuadraticSphereRigidity
