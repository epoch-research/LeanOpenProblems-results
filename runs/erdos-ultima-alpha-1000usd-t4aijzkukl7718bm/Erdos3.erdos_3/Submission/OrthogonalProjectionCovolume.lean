import Submission.KernelShearLattice
import Submission.PrimitiveKernelCovolume

/-! Covolume of the orthogonal projection of a lattice along a primitive vector.
The functional defining the orthogonal hyperplane need not be integral. -/
namespace Erdos3OrthogonalProjectionCovolume
open Finset Module MeasureTheory Erdos3KernelProjectionEstimates
  Erdos3PrimitiveKernelLattice Erdos3PrimitiveLatticeSplitting
  Erdos3NormalOrthonormalBasis Erdos3PrimitiveKernelCovolume Erdos3KernelShearLattice
open scoped BigOperators RealInnerProductSpace Classical
set_option maxHeartbeats 4000000

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma projected_basis_determinant (L : Submodule ℤ E) (F G : E →L[ℝ] ℝ)
    (hG0 : G ≠ 0) (v : E) (hF : F v = 1) (hG : G v = 1)
    (hint : ∀ y : E, y ∈ L → ∃ c : ℤ, F y = (c : ℝ)) (hvL : v ∈ L)
    (horth : ∀ x : E, G x = 0 → ⟪x,v⟫ = 0)
    (b : Basis I ℤ (kernelLattice L F)) (o : OrthonormalBasis I ℝ G.toLinearMap.ker) :
    (splitOrthonormalBasis G hG0 o).toBasis.det
      (fun i ↦ (adaptedLatticeBasis L F hint v hvL hF b i : E)) =
      (1/‖G‖)*o.toBasis.det
        (fun i ↦ (projectedBasis L F G v hF hG b i : G.toLinearMap.ker)) := by
  let A : Matrix Unit Unit ℝ := fun _ _ ↦ 1/‖G‖
  let B : Matrix Unit I ℝ := fun _ j ↦ G ((b j : F.toLinearMap.ker) : E)/‖G‖
  let D : Matrix I I ℝ := o.toBasis.toMatrix
    (fun i ↦ (projectedBasis L F G v hF hG b i : G.toLinearMap.ker))
  have ho (i : I) : ⟪(o i : E),v⟫ = 0 := horth (o i) (o i).property
  have hproj (i j : I) :
      ⟪(o i : E),((projectedBasis L F G v hF hG b j : G.toLinearMap.ker) : E)⟫ =
        ⟪(o i : E),((b j : F.toLinearMap.ker) : E)⟫ := by
    rw [projectedBasis_apply,projectionAlong_apply,inner_sub_right,real_inner_smul_right,
      ho,mul_zero,sub_zero]
  have hM : (splitOrthonormalBasis G hG0 o).toBasis.toMatrix
      (fun i ↦ (adaptedLatticeBasis L F hint v hvL hF b i : E)) =
      Matrix.fromBlocks A B 0 D := by
    ext i j
    cases i <;> cases j <;>
      simp only [Basis.toMatrix_apply,OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply,splitOrthonormalBasis_left,splitOrthonormalBasis_right,
        adaptedLatticeBasis_left,adaptedLatticeBasis_right,Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
        unitNormal_inner,hG,ho,Matrix.zero_apply,A,B,D]
    exact (hproj _ _).symm
  rw [Basis.det_apply,hM,Matrix.det_fromBlocks_zero₂₁,Matrix.det_unique]
  rfl

theorem orthogonal_projection_covolume_of_basis (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (F G : E →L[ℝ] ℝ)
    (hG0 : G ≠ 0) (v : E) (hF : F v = 1) (hG : G v = 1)
    (hint : ∀ y : E, y ∈ L → ∃ c : ℤ, F y = (c : ℝ)) (hvL : v ∈ L)
    (horth : ∀ x : E, G x = 0 → ⟪x,v⟫ = 0)
    (b : Basis I ℤ (kernelLattice L F)) (o : OrthonormalBasis I ℝ G.toLinearMap.ker) :
    ZLattice.covolume (projectedLattice L F G v hF hG) = ‖G‖*ZLattice.covolume L := by
  letI : IsZLattice ℝ (projectedLattice L F G v hF hG) :=
    projectedLattice_isZLattice L F G v hF hG hint hvL
  have hvol : ZLattice.covolume L =
      (1/‖G‖)*ZLattice.covolume (projectedLattice L F G v hF hG) := by
    rw [covolume_eq_orthonormal_det L (adaptedLatticeBasis L F hint v hvL hF b)
        (splitOrthonormalBasis G hG0 o),
      projected_basis_determinant L F G hG0 v hF hG hint hvL horth b o,
      abs_mul,abs_of_nonneg (one_div_nonneg.mpr (norm_nonneg G)),
      covolume_eq_orthonormal_det (projectedLattice L F G v hF hG)
        (projectedBasis L F G v hF hG b) o]
  rw [hvol]
  field_simp

theorem orthogonal_projection_covolume (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (F G : E →L[ℝ] ℝ)
    (hG0 : G ≠ 0) (v : E) (hF : F v = 1) (hG : G v = 1)
    (hint : ∀ y : E, y ∈ L → ∃ c : ℤ, F y = (c : ℝ)) (hvL : v ∈ L)
    (horth : ∀ x : E, G x = 0 → ⟪x,v⟫ = 0) :
    ZLattice.covolume (projectedLattice L F G v hF hG) = ‖G‖*ZLattice.covolume L := by
  letI : IsZLattice ℝ (kernelLattice L F) := kernelLattice_isZLattice L F hint v hvL hF
  let J := Free.ChooseBasisIndex ℤ (kernelLattice L F)
  let b := Free.chooseBasis ℤ (kernelLattice L F)
  have hdim : finrank ℝ F.toLinearMap.ker = finrank ℝ G.toLinearMap.ker := by
    have hf := kernel_finrank F v hF
    have hg := kernel_finrank G v hG
    omega
  have hcard : Fintype.card J = finrank ℝ G.toLinearMap.ker := by
    dsimp only [J]
    rw [← finrank_eq_card_chooseBasisIndex,ZLattice.rank ℝ,hdim]
  let e : Fin (finrank ℝ G.toLinearMap.ker) ≃ J :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin,hcard])
  let o := (stdOrthonormalBasis ℝ G.toLinearMap.ker).reindex e
  exact orthogonal_projection_covolume_of_basis L F G hG0 v hF hG hint hvL horth b o

noncomputable def vectorFunctional (v : E) : E →L[ℝ] ℝ :=
  (‖v‖^2)⁻¹ • (InnerProductSpace.toDual ℝ E v)

lemma vectorFunctional_apply (v x : E) : vectorFunctional v x = ⟪v,x⟫/(‖v‖^2) := by
  simp only [vectorFunctional,ContinuousLinearMap.smul_apply,
    InnerProductSpace.toDual_apply_apply,smul_eq_mul]
  ring

lemma vectorFunctional_self (v : E) (hv : v ≠ 0) : vectorFunctional v v = 1 := by
  rw [vectorFunctional_apply,real_inner_self_eq_norm_sq,div_self]
  exact pow_ne_zero _ (norm_ne_zero_iff.mpr hv)

lemma vectorFunctional_norm (v : E) (hv : v ≠ 0) : ‖vectorFunctional v‖ = 1/‖v‖ := by
  rw [vectorFunctional,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _)),(InnerProductSpace.toDual ℝ E).norm_map]
  have hn := norm_ne_zero_iff.mpr hv
  field_simp

lemma vectorFunctional_orthogonal (v x : E) (hv : v ≠ 0) (hx : vectorFunctional v x = 0) :
    ⟪x,v⟫ = 0 := by
  rw [vectorFunctional_apply,div_eq_zero_iff] at hx
  rcases hx with hx | hx
  · rwa [real_inner_comm]
  · exact (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv) hx).elim

/-- Projection along a primitive vector divides lattice covolume by its length. -/
theorem primitive_vector_projection_covolume (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (F : E →L[ℝ] ℝ)
    (v : E) (hv0 : v ≠ 0) (hF : F v = 1)
    (hint : ∀ y : E, y ∈ L → ∃ c : ℤ, F y = (c : ℝ)) (hvL : v ∈ L) :
    ZLattice.covolume (projectedLattice L F (vectorFunctional v) v hF (vectorFunctional_self v hv0)) =
      ZLattice.covolume L/‖v‖ := by
  have hG0 : vectorFunctional v ≠ 0 := by
    intro hz
    have hh := vectorFunctional_self v hv0
    simp [hz] at hh
  rw [orthogonal_projection_covolume L F (vectorFunctional v) hG0 v hF
      (vectorFunctional_self v hv0) hint hvL (fun x hx ↦ vectorFunctional_orthogonal v x hv0 hx),
    vectorFunctional_norm v hv0]
  ring

#print axioms primitive_vector_projection_covolume
end Erdos3OrthogonalProjectionCovolume
