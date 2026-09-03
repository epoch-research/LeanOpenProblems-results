import Submission.PrimitiveKernelLattice

/-! Shearing between two complementary hyperplanes along the same primitive
lattice vector. This makes projection of a lattice into a different hyperplane
an actual full discrete lattice, and gives its basis explicitly. -/
namespace Erdos3KernelShearLattice
open Module Erdos3KernelProjectionEstimates Erdos3PrimitiveKernelLattice
open scoped Classical
set_option maxHeartbeats 3000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma projectionAlong_comp (F G : E →L[ℝ] ℝ) (v : E) (hF : F v = 1) (x : E) :
    projectionAlong F v (projectionAlong G v x) = projectionAlong F v x := by
  simp only [projectionAlong_apply,map_sub,map_smul,hF,smul_eq_mul,mul_one]
  module

noncomputable def kernelShear (F G : E →L[ℝ] ℝ) (v : E) (hF : F v = 1) (hG : G v = 1) :
    F.toLinearMap.ker ≃L[ℝ] G.toLinearMap.ker where
  toFun x := projectToKernel G v hG x
  invFun y := projectToKernel F v hF y
  left_inv x := by
    apply Subtype.ext
    change projectionAlong F v (projectionAlong G v x) = (x : E)
    rw [projectionAlong_comp F G v hF,projectionAlong_eq_self F v x x.property]
  right_inv y := by
    apply Subtype.ext
    change projectionAlong G v (projectionAlong F v y) = (y : E)
    rw [projectionAlong_comp G F v hG,projectionAlong_eq_self G v y y.property]
  map_add' x y := by simp only [Submodule.coe_add,map_add]
  map_smul' c x := by simp only [Submodule.coe_smul,map_smul,RingHom.id_apply]
  continuous_toFun := (projectToKernel G v hG).continuous.comp continuous_subtype_val
  continuous_invFun := (projectToKernel F v hF).continuous.comp continuous_subtype_val

lemma kernelShear_apply (F G : E →L[ℝ] ℝ) (v : E) (hF : F v = 1) (hG : G v = 1)
    (x : F.toLinearMap.ker) :
    (kernelShear F G v hF hG x : E) = projectionAlong G v x := rfl

lemma kernelShear_symm_apply (F G : E →L[ℝ] ℝ) (v : E) (hF : F v = 1) (hG : G v = 1)
    (y : G.toLinearMap.ker) :
    ((kernelShear F G v hF hG).symm y : E) = projectionAlong F v y := rfl

noncomputable def projectedLattice (L : Submodule ℤ E) (F G : E →L[ℝ] ℝ)
    (v : E) (hF : F v = 1) (hG : G v = 1) : Submodule ℤ G.toLinearMap.ker :=
  ZLattice.comap ℝ (kernelLattice L F) (kernelShear F G v hF hG).symm.toLinearEquiv.toLinearMap

instance projectedLattice_discrete (L : Submodule ℤ E) [DiscreteTopology L]
    (F G : E →L[ℝ] ℝ) (v : E) (hF : F v = 1) (hG : G v = 1) :
    DiscreteTopology (projectedLattice L F G v hF hG) := by
  exact ZLattice.comap_discreteTopology ℝ (kernelLattice L F)
    (kernelShear F G v hF hG).symm.continuous (kernelShear F G v hF hG).symm.injective

lemma mem_projectedLattice (L : Submodule ℤ E) (F G : E →L[ℝ] ℝ)
    (v : E) (hF : F v = 1) (hG : G v = 1) (y : G.toLinearMap.ker) :
    y ∈ projectedLattice L F G v hF hG ↔ projectionAlong F v y ∈ L := Iff.rfl

theorem projectedLattice_isZLattice (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (F G : E →L[ℝ] ℝ) (v : E) (hF : F v = 1) (hG : G v = 1)
    (hint : ∀ y : E, y ∈ L → ∃ c : ℤ, F y = (c : ℝ)) (hvL : v ∈ L) :
    IsZLattice ℝ (projectedLattice L F G v hF hG) := by
  letI : IsZLattice ℝ (kernelLattice L F) := kernelLattice_isZLattice L F hint v hvL hF
  exact inferInstanceAs (IsZLattice ℝ (ZLattice.comap ℝ (kernelLattice L F)
    (kernelShear F G v hF hG).symm.toLinearMap))

/-- The constructed lattice is precisely the projection of L along v. -/
theorem projectedLattice_mem_iff (L : Submodule ℤ E) (F G : E →L[ℝ] ℝ)
    (v : E) (hF : F v = 1) (hG : G v = 1)
    (hint : ∀ y : E, y ∈ L → ∃ c : ℤ, F y = (c : ℝ)) (hvL : v ∈ L)
    (y : G.toLinearMap.ker) :
    y ∈ projectedLattice L F G v hF hG ↔ ∃ x : E, x ∈ L ∧ projectionAlong G v x = (y : E) := by
  rw [mem_projectedLattice]
  constructor
  · intro hy
    refine ⟨projectionAlong F v y,hy,?_⟩
    rw [projectionAlong_comp G F v hG,projectionAlong_eq_self G v y y.property]
  · rintro ⟨x,hx,hxy⟩
    rw [← hxy,projectionAlong_comp F G v hF]
    obtain ⟨c,hc⟩ := hint x hx
    rw [projectionAlong_apply,hc,Int.cast_smul_eq_zsmul ℝ]
    exact L.sub_mem hx (L.smul_mem c hvL)

noncomputable def projectedBasis {I : Type*} (L : Submodule ℤ E) (F G : E →L[ℝ] ℝ)
    (v : E) (hF : F v = 1) (hG : G v = 1) (b : Basis I ℤ (kernelLattice L F)) :
    Basis I ℤ (projectedLattice L F G v hF hG) :=
  b.ofZLatticeComap ℝ (kernelLattice L F) (kernelShear F G v hF hG).symm.toLinearEquiv

lemma projectedBasis_apply {I : Type*} (L : Submodule ℤ E) (F G : E →L[ℝ] ℝ)
    (v : E) (hF : F v = 1) (hG : G v = 1) (b : Basis I ℤ (kernelLattice L F)) (i : I) :
    ((projectedBasis L F G v hF hG b i : G.toLinearMap.ker) : E) =
      projectionAlong G v ((b i : F.toLinearMap.ker) : E) := by
  simp only [projectedBasis,Basis.ofZLatticeComap_apply]
  rfl

#print axioms projectedLattice_isZLattice
#print axioms projectedLattice_mem_iff
end Erdos3KernelShearLattice
