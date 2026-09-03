import Submission.ShortLiftLatticeBasis
import Submission.ShortestLatticeVector
import Submission.OrthogonalProjectionCovolume

/-! A dimension-only bound for the product of the lengths of an integer lattice
basis. The proof is by shortest-vector projection, rounded lifting, and the exact
projection-covolume identity. -/
namespace Erdos3ReducedLatticeBasis
open Finset Module MeasureTheory Erdos3KernelProjectionEstimates
  Erdos3PrimitiveKernelLattice Erdos3KernelShearLattice
  Erdos3PrimitiveKernelCovolume Erdos3OrthogonalProjectionCovolume
  Erdos3ShortLiftLatticeBasis Erdos3ShortestLatticeVector
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

universe u

noncomputable def finLatticeBasis {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (n : ℕ) (hn : finrank ℝ E = n) : Basis (Fin n) ℤ L :=
  (finBasis ℤ L).reindex (Fintype.equivOfCardEq (by simp [ZLattice.rank ℝ L,hn]))

lemma latticeBasis_prod_reindex {I J E : Type*} [Fintype I] [Fintype J]
    [NormedAddCommGroup E] (L : Submodule ℤ E) (b : Basis I ℤ L) (e : I ≃ J) :
    (∏ j, ‖(b.reindex e j : E)‖) = ∏ i, ‖(b i : E)‖ := by
  exact Fintype.prod_equiv e.symm _ _ (fun j ↦ by rw [Basis.reindex_apply])

private theorem exists_reduced_basis_aux (n : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E]
      (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L],
      finrank ℝ E = n →
      ∃ b : Basis (Fin n) ℤ L, (∏ i, ‖(b i : E)‖) ≤ (2:ℝ)^(n*n)*ZLattice.covolume L := by
  induction n with
  | zero =>
    intro E _ _ _ _ _ L _ _ hn
    let b := finLatticeBasis L 0 hn
    let e : Fin (finrank ℝ E) ≃ Fin 0 := Fintype.equivOfCardEq (by simp [hn])
    let o := (stdOrthonormalBasis ℝ E).reindex e
    refine ⟨b,?_⟩
    rw [covolume_eq_orthonormal_det L b o]
    simp [Basis.det_apply,Matrix.det_isEmpty]
  | succ n ih =>
    intro E _ _ _ _ _ L _ _ hn
    let binit := finLatticeBasis L (n+1) hn
    have hL : L ≠ ⊥ := by
      apply L.ne_bot_iff.mpr
      refine ⟨(binit 0 : E),(binit 0).property,?_⟩
      intro hz
      exact binit.ne_zero 0 (Subtype.ext hz)
    obtain ⟨v,hvL,hv0,hmin⟩ := exists_shortest_lattice_vector L hL
    obtain ⟨F,hF,hint⟩ := shortest_vector_primitive L v hvL hv0 hmin
    let G := vectorFunctional v
    have hG : G v = 1 := vectorFunctional_self v hv0
    let P := projectedLattice L F G v hF hG
    letI : IsZLattice ℝ P := projectedLattice_isZLattice L F G v hF hG hint hvL
    have hdim : finrank ℝ G.toLinearMap.ker = n := by
      have hd := kernel_finrank G v hG
      omega
    obtain ⟨b,hb⟩ := ih G.toLinearMap.ker P hdim
    obtain ⟨B,hB⟩ := short_lift_basis_product L F G v hF hG hint hvL hmin b
    have hvol : ZLattice.covolume P = ZLattice.covolume L/‖v‖ :=
      primitive_vector_projection_covolume L F v hv0 hF hint hvL
    let e : Unit ⊕ Fin n ≃ Fin (n+1) := Fintype.equivOfCardEq (by simp; omega)
    refine ⟨B.reindex e,?_⟩
    rw [latticeBasis_prod_reindex L B e]
    calc
      _ ≤ ‖v‖*2^n*(∏ i, ‖(b i : G.toLinearMap.ker)‖) := by simpa only [Fintype.card_fin] using hB
      _ ≤ ‖v‖*2^n*((2:ℝ)^(n*n)*ZLattice.covolume P) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (2:ℝ)^(n+n*n)*ZLattice.covolume L := by
        rw [hvol,pow_add]
        have hvn := norm_ne_zero_iff.mpr hv0
        field_simp
      _ ≤ (2:ℝ)^((n+1)*(n+1))*ZLattice.covolume L :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show n+n*n ≤ (n+1)*(n+1) by nlinarith))
          (ZLattice.covolume_pos L).le
    all_goals exact le_rfl

/-- Every full Euclidean lattice has an integer basis with dimension-only
orthogonality defect at most 2^(dimension^2). -/
theorem exists_reduced_lattice_basis {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ b : Basis (Fin (finrank ℝ E)) ℤ L,
      (∏ i, ‖(b i : E)‖) ≤ (2:ℝ)^((finrank ℝ E)^2)*ZLattice.covolume L := by
  simpa only [pow_two] using exists_reduced_basis_aux (finrank ℝ E) E L rfl

#print axioms exists_reduced_lattice_basis
end Erdos3ReducedLatticeBasis
