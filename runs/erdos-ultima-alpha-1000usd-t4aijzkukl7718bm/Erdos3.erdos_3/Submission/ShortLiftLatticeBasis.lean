import Submission.RoundedLatticeLift
import Submission.PrimitiveLatticeSplitting

/-! A basis of a projected lattice lifts to a basis of the original lattice.
Rounding by integer multiples of a shortest vector costs at most a factor two
in the lengths of the lifted basis vectors. -/
namespace Erdos3ShortLiftLatticeBasis
open Module Erdos3KernelProjectionEstimates Erdos3PrimitiveKernelLattice
  Erdos3PrimitiveLatticeSplitting Erdos3KernelShearLattice Erdos3RoundedLatticeLift
open scoped Classical BigOperators
set_option maxHeartbeats 3000000

section Shear
variable {M : Type*} [AddCommGroup M] [Module ℤ M]

noncomputable def upperShear (T : M →ₗ[ℤ] ℤ) : (ℤ × M) ≃ₗ[ℤ] (ℤ × M) where
  toFun p := (p.1-T p.2,p.2)
  invFun p := (p.1+T p.2,p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' p q := by
    ext
    · change (p.1+q.1)-T (p.2+q.2) = (p.1-T p.2)+(q.1-T q.2)
      rw [map_add]; abel
    · rfl
  map_smul' c p := by
    ext
    · change c*p.1-T (c • p.2) = c*(p.1-T p.2)
      rw [map_zsmul,zsmul_eq_mul,Int.cast_id,mul_sub]
    · rfl

lemma upperShear_apply (T : M →ₗ[ℤ] ℤ) (p : ℤ × M) :
    upperShear T p = (p.1-T p.2,p.2) := rfl
end Shear

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def shearedLatticeBasis (L : Submodule ℤ E) (F : E →L[ℝ] ℝ)
    (hint : ∀ y : E, y ∈ L → ∃ c : ℤ, F y = (c : ℝ))
    (v : E) (hvL : v ∈ L) (hv : F v = 1)
    (b : Basis I ℤ (kernelLattice L F)) (c : I → ℤ) : Basis (Unit ⊕ I) ℤ L :=
  ((Basis.singleton Unit ℤ).prod b).map
    ((upperShear (b.constr ℤ c)).trans (latticeSplitEquiv L F hint v hvL hv))

lemma shearedLatticeBasis_left (L : Submodule ℤ E) (F : E →L[ℝ] ℝ)
    (hint : ∀ y : E, y ∈ L → ∃ c : ℤ, F y = (c : ℝ))
    (v : E) (hvL : v ∈ L) (hv : F v = 1)
    (b : Basis I ℤ (kernelLattice L F)) (c : I → ℤ) (i : Unit) :
    (shearedLatticeBasis L F hint v hvL hv b c (Sum.inl i) : E) = v := by
  simp [shearedLatticeBasis,upperShear_apply,latticeSplitEquiv,
    LinearEquiv.ofBijective_apply,latticeJoin_apply]

lemma shearedLatticeBasis_right (L : Submodule ℤ E) (F : E →L[ℝ] ℝ)
    (hint : ∀ y : E, y ∈ L → ∃ c : ℤ, F y = (c : ℝ))
    (v : E) (hvL : v ∈ L) (hv : F v = 1)
    (b : Basis I ℤ (kernelLattice L F)) (c : I → ℤ) (i : I) :
    (shearedLatticeBasis L F hint v hvL hv b c (Sum.inr i) : E) =
      ((b i : F.toLinearMap.ker) : E)-c i • v := by
  simp [shearedLatticeBasis,upperShear_apply,latticeSplitEquiv,
    LinearEquiv.ofBijective_apply,latticeJoin_apply,sub_eq_add_neg,add_comm]

noncomputable def pullbackProjectedBasis (L : Submodule ℤ E) (F G : E →L[ℝ] ℝ)
    (v : E) (hF : F v = 1) (hG : G v = 1)
    (b : Basis I ℤ (projectedLattice L F G v hF hG)) : Basis I ℤ (kernelLattice L F) :=
  b.map (ZLattice.comap_equiv ℝ (kernelLattice L F)
    (kernelShear F G v hF hG).symm.toLinearEquiv).symm

lemma projected_pullback_basis (L : Submodule ℤ E) (F G : E →L[ℝ] ℝ)
    (v : E) (hF : F v = 1) (hG : G v = 1)
    (b : Basis I ℤ (projectedLattice L F G v hF hG)) :
    projectedBasis L F G v hF hG (pullbackProjectedBasis L F G v hF hG b) = b := by
  let e := ZLattice.comap_equiv ℝ (kernelLattice L F)
    (kernelShear F G v hF hG).symm.toLinearEquiv
  ext i
  change ((e (e.symm (b i)) : G.toLinearMap.ker) : E) = ((b i : G.toLinearMap.ker) : E)
  rw [e.apply_symm_apply]

lemma pullback_basis_projection (L : Submodule ℤ E) (F G : E →L[ℝ] ℝ)
    (v : E) (hF : F v = 1) (hG : G v = 1)
    (b : Basis I ℤ (projectedLattice L F G v hF hG)) (i : I) :
    projectionAlong G v ((pullbackProjectedBasis L F G v hF hG b i : F.toLinearMap.ker) : E) =
      ((b i : G.toLinearMap.ker) : E) := by
  rw [← projectedBasis_apply,projected_pullback_basis]

/-- A projected basis has an actual integer basis lift with controlled lengths. -/
theorem exists_short_lift_basis (L : Submodule ℤ E) (F G : E →L[ℝ] ℝ)
    (v : E) (hF : F v = 1) (hG : G v = 1)
    (hint : ∀ y : E, y ∈ L → ∃ c : ℤ, F y = (c : ℝ)) (hvL : v ∈ L)
    (hmin : ∀ y : E, y ∈ L → y ≠ 0 → ‖v‖ ≤ ‖y‖)
    (b : Basis I ℤ (projectedLattice L F G v hF hG)) :
    ∃ B : Basis (Unit ⊕ I) ℤ L,
      (∀ i : Unit, (B (Sum.inl i) : E) = v) ∧
      (∀ i : I, projectionAlong G v (B (Sum.inr i) : E) = ((b i : G.toLinearMap.ker) : E)) ∧
      (∀ i : I, ‖(B (Sum.inr i) : E)‖ ≤ 2*‖(b i : G.toLinearMap.ker)‖) := by
  let b₀ := pullbackProjectedBasis L F G v hF hG b
  let c : I → ℤ := fun i ↦ round (G ((b₀ i : F.toLinearMap.ker) : E))
  let B := shearedLatticeBasis L F hint v hvL hF b₀ c
  have hB (i : I) : (B (Sum.inr i) : E) = roundedLift G v ((b₀ i : F.toLinearMap.ker) : E) :=
    shearedLatticeBasis_right L F hint v hvL hF b₀ c i
  have hproj (i : I) : projectionAlong G v ((b₀ i : F.toLinearMap.ker) : E) =
      ((b i : G.toLinearMap.ker) : E) := pullback_basis_projection L F G v hF hG b i
  refine ⟨B,fun i ↦ shearedLatticeBasis_left L F hint v hvL hF b₀ c i,?_,?_⟩
  · intro i
    rw [hB,roundedLift_projection G v _ hG,hproj]
  · intro i
    have hne : ((b i : G.toLinearMap.ker) : E) ≠ 0 := by
      intro hz
      apply b.ne_zero i
      apply Subtype.ext
      exact Subtype.ext hz
    have hn := (shortest_roundedLift_norm L G v ((b₀ i : F.toLinearMap.ker) : E)
      hvL hG (b₀ i).property hmin (by rwa [hproj])).1
    rw [hB]
    simpa only [hproj] using hn

/-- The product cost of lifting is at most 2 to the projected dimension. -/
theorem short_lift_basis_product (L : Submodule ℤ E) (F G : E →L[ℝ] ℝ)
    (v : E) (hF : F v = 1) (hG : G v = 1)
    (hint : ∀ y : E, y ∈ L → ∃ c : ℤ, F y = (c : ℝ)) (hvL : v ∈ L)
    (hmin : ∀ y : E, y ∈ L → y ≠ 0 → ‖v‖ ≤ ‖y‖)
    (b : Basis I ℤ (projectedLattice L F G v hF hG)) :
    ∃ B : Basis (Unit ⊕ I) ℤ L,
      (∏ i, ‖(B i : E)‖) ≤ ‖v‖*2^(Fintype.card I)*(∏ i, ‖(b i : G.toLinearMap.ker)‖) := by
  obtain ⟨B,hleft,_,hright⟩ := exists_short_lift_basis L F G v hF hG hint hvL hmin b
  refine ⟨B,?_⟩
  rw [Fintype.prod_sum_type]
  simp only [hleft,Finset.prod_const,Fintype.card_unique,Finset.card_univ,pow_one]
  calc
    _ ≤ ‖v‖*(∏ i, 2*‖(b i : G.toLinearMap.ker)‖) :=
      mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _ ↦ norm_nonneg _) (fun i _ ↦ hright i))
        (norm_nonneg _)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]; ring

#print axioms short_lift_basis_product
end Erdos3ShortLiftLatticeBasis
