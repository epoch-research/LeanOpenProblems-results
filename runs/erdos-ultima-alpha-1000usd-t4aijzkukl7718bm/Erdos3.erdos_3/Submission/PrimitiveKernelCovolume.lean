import Submission.PrimitiveLatticeSplitting
import Submission.NormalOrthonormalBasis

/-! Exact covolume change under primitive kernel reduction. The formula is
covolume(L intersect ker F)=norm(F)*covolume(L); no integer denominator enters
this geometric cost. -/
namespace Erdos3PrimitiveKernelCovolume
open Finset Module MeasureTheory Erdos3PrimitiveKernelLattice
  Erdos3PrimitiveLatticeSplitting Erdos3NormalOrthonormalBasis
open scoped BigOperators RealInnerProductSpace Classical
set_option maxHeartbeats 4000000

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma orthonormal_fundamental_volume (o : OrthonormalBasis I ℝ E) :
    volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
  rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume)]
  change (volume (parallelepiped (fun i ↦ o i))).toReal = 1
  rw [o.volume_parallelepiped]
  rfl

lemma covolume_eq_orthonormal_det (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis I ℤ L) (o : OrthonormalBasis I ℝ E) :
    ZLattice.covolume L = |o.toBasis.det (fun i ↦ (b i : E))| := by
  rw [ZLattice.covolume_eq_det_mul_measureReal L volume b o.toBasis,
    orthonormal_fundamental_volume,mul_one]
  rfl

lemma adapted_basis_determinant (L : Submodule ℤ E) (F : E →L[ℝ] ℝ) (hF : F ≠ 0)
    (hint : ∀ y : E, y ∈ L → ∃ c : ℤ, F y = (c : ℝ))
    (v : E) (hvL : v ∈ L) (hv : F v = 1)
    (b : Basis I ℤ (kernelLattice L F)) (o : OrthonormalBasis I ℝ F.toLinearMap.ker) :
    (splitOrthonormalBasis F hF o).toBasis.det
      (fun i ↦ (adaptedLatticeBasis L F hint v hvL hv b i : E)) =
      (1/‖F‖)*o.toBasis.det (fun i ↦ (b i : F.toLinearMap.ker)) := by
  let A : Matrix Unit Unit ℝ := fun _ _ ↦ 1/‖F‖
  let C : Matrix I Unit ℝ := fun i _ ↦ ⟪(o i : E),v⟫
  let D : Matrix I I ℝ := o.toBasis.toMatrix (fun i ↦ (b i : F.toLinearMap.ker))
  have hbzero (i : I) : F ((b i : F.toLinearMap.ker) : E) = 0 :=
    (b i : F.toLinearMap.ker).property
  have hM : (splitOrthonormalBasis F hF o).toBasis.toMatrix
      (fun i ↦ (adaptedLatticeBasis L F hint v hvL hv b i : E)) =
      Matrix.fromBlocks A 0 C D := by
    ext i j
    cases i <;> cases j <;>
      simp only [Basis.toMatrix_apply,OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply,splitOrthonormalBasis_left,splitOrthonormalBasis_right,
        adaptedLatticeBasis_left,adaptedLatticeBasis_right,Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
        unitNormal_inner,hv,hbzero,zero_div,Matrix.zero_apply,A,C,D]
    rfl
  rw [Basis.det_apply,hM,Matrix.det_fromBlocks_zero₁₂,Matrix.det_unique]
  rfl

/-- Basis-indexed form of the primitive kernel covolume identity. -/
theorem primitive_kernel_covolume_of_basis (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (F : E →L[ℝ] ℝ) (hF : F ≠ 0)
    (hint : ∀ y : E, y ∈ L → ∃ c : ℤ, F y = (c : ℝ))
    (v : E) (hvL : v ∈ L) (hv : F v = 1)
    (b : Basis I ℤ (kernelLattice L F)) (o : OrthonormalBasis I ℝ F.toLinearMap.ker) :
    ZLattice.covolume (kernelLattice L F) = ‖F‖*ZLattice.covolume L := by
  letI : IsZLattice ℝ (kernelLattice L F) := kernelLattice_isZLattice L F hint v hvL hv
  have hvol : ZLattice.covolume L = (1/‖F‖)*ZLattice.covolume (kernelLattice L F) := by
    rw [covolume_eq_orthonormal_det L (adaptedLatticeBasis L F hint v hvL hv b) (splitOrthonormalBasis F hF o),
      adapted_basis_determinant,abs_mul,abs_of_nonneg (one_div_nonneg.mpr (norm_nonneg F)),
      covolume_eq_orthonormal_det (kernelLattice L F) b o]
  rw [hvol]
  field_simp

/-- Primitive kernel reduction costs exactly the norm of the dual functional. -/
theorem primitive_kernel_covolume (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (F : E →L[ℝ] ℝ) (hF : F ≠ 0)
    (hint : ∀ y : E, y ∈ L → ∃ c : ℤ, F y = (c : ℝ))
    (v : E) (hvL : v ∈ L) (hv : F v = 1) :
    ZLattice.covolume (kernelLattice L F) = ‖F‖*ZLattice.covolume L := by
  letI : IsZLattice ℝ (kernelLattice L F) := kernelLattice_isZLattice L F hint v hvL hv
  let J := Free.ChooseBasisIndex ℤ (kernelLattice L F)
  let b := Free.chooseBasis ℤ (kernelLattice L F)
  have hcard : Fintype.card J = finrank ℝ F.toLinearMap.ker := by
    dsimp only [J]
    rw [← finrank_eq_card_chooseBasisIndex,ZLattice.rank ℝ]
  let e : Fin (finrank ℝ F.toLinearMap.ker) ≃ J :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin,hcard])
  let o := (stdOrthonormalBasis ℝ F.toLinearMap.ker).reindex e
  exact primitive_kernel_covolume_of_basis L F hF hint v hvL hv b o

#print axioms primitive_kernel_covolume
end Erdos3PrimitiveKernelCovolume
