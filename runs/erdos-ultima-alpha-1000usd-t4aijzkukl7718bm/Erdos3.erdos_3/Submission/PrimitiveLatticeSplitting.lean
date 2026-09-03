import Submission.PrimitiveKernelLattice

/-! An integral direct-sum decomposition of a lattice along a primitive
functional. This produces an adapted integer basis for determinant and
covolume comparisons. -/
namespace Erdos3PrimitiveLatticeSplitting
open Module Erdos3PrimitiveKernelLattice
open scoped Classical
set_option maxHeartbeats 3000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def latticeJoin (L : Submodule ℤ E) (F : E →L[ℝ] ℝ)
    (v : E) (hvL : v ∈ L) : (ℤ × kernelLattice L F) →ₗ[ℤ] L where
  toFun p := ⟨p.1 • v+((p.2 : F.toLinearMap.ker) : E),L.add_mem (L.smul_mem _ hvL) p.2.property⟩
  map_add' p q := by
    apply Subtype.ext
    change (p.1+q.1) • v+(((p.2 : F.toLinearMap.ker) : E)+((q.2 : F.toLinearMap.ker) : E)) = _
    simp only [add_smul,Submodule.coe_add]
    abel
  map_smul' c p := by
    apply Subtype.ext
    change (c*p.1) • v+c • ((p.2 : F.toLinearMap.ker) : E) = c • (p.1 • v+((p.2 : F.toLinearMap.ker) : E))
    rw [smul_add,smul_smul]

lemma latticeJoin_apply (L : Submodule ℤ E) (F : E →L[ℝ] ℝ)
    (v : E) (hvL : v ∈ L) (p : ℤ × kernelLattice L F) :
    (latticeJoin L F v hvL p : E) = p.1 • v+((p.2 : F.toLinearMap.ker) : E) := rfl

lemma latticeJoin_bijective (L : Submodule ℤ E) (F : E →L[ℝ] ℝ)
    (hint : ∀ y : E, y ∈ L → ∃ c : ℤ, F y = (c : ℝ))
    (v : E) (hvL : v ∈ L) (hv : F v = 1) :
    Function.Bijective (latticeJoin L F v hvL) := by
  constructor
  · intro p q hpq
    have he : p.1 • v+((p.2 : F.toLinearMap.ker) : E) = q.1 • v+((q.2 : F.toLinearMap.ker) : E) :=
      congrArg (fun x : L ↦ (x : E)) hpq
    have hFhe := congrArg F he
    have hp0 : F ((p.2 : F.toLinearMap.ker) : E) = 0 := (p.2 : F.toLinearMap.ker).property
    have hq0 : F ((q.2 : F.toLinearMap.ker) : E) = 0 := (q.2 : F.toLinearMap.ker).property
    simp only [map_add,map_zsmul,hv,hp0,hq0,zsmul_eq_mul,mul_one,add_zero] at hFhe
    have hfst : p.1 = q.1 := by exact_mod_cast hFhe
    apply Prod.ext hfst
    apply Subtype.ext
    apply Subtype.ext
    rw [hfst] at he
    exact add_left_cancel he
  · intro x
    obtain ⟨c,hc⟩ := hint x x.property
    have hzero : F ((x : E)-c • v) = 0 := by
      rw [map_sub,map_zsmul,hc,hv,zsmul_eq_mul,mul_one,sub_self]
    let y : kernelLattice L F := ⟨⟨(x : E)-c • v,hzero⟩,L.sub_mem x.property (L.smul_mem c hvL)⟩
    refine ⟨(c,y),?_⟩
    apply Subtype.ext
    change c • v+((x : E)-c • v) = (x : E)
    abel

noncomputable def latticeSplitEquiv (L : Submodule ℤ E) (F : E →L[ℝ] ℝ)
    (hint : ∀ y : E, y ∈ L → ∃ c : ℤ, F y = (c : ℝ))
    (v : E) (hvL : v ∈ L) (hv : F v = 1) :
    (ℤ × kernelLattice L F) ≃ₗ[ℤ] L :=
  LinearEquiv.ofBijective (latticeJoin L F v hvL) (latticeJoin_bijective L F hint v hvL hv)

noncomputable def adaptedLatticeBasis {I : Type*} (L : Submodule ℤ E) (F : E →L[ℝ] ℝ)
    (hint : ∀ y : E, y ∈ L → ∃ c : ℤ, F y = (c : ℝ))
    (v : E) (hvL : v ∈ L) (hv : F v = 1)
    (b : Basis I ℤ (kernelLattice L F)) : Basis (Unit ⊕ I) ℤ L :=
  ((Basis.singleton Unit ℤ).prod b).map (latticeSplitEquiv L F hint v hvL hv)

lemma adaptedLatticeBasis_left {I : Type*} (L : Submodule ℤ E) (F : E →L[ℝ] ℝ)
    (hint : ∀ y : E, y ∈ L → ∃ c : ℤ, F y = (c : ℝ))
    (v : E) (hvL : v ∈ L) (hv : F v = 1)
    (b : Basis I ℤ (kernelLattice L F)) (i : Unit) :
    (adaptedLatticeBasis L F hint v hvL hv b (Sum.inl i) : E) = v := by
  simp [adaptedLatticeBasis,latticeSplitEquiv,LinearEquiv.ofBijective_apply,latticeJoin_apply]

lemma adaptedLatticeBasis_right {I : Type*} (L : Submodule ℤ E) (F : E →L[ℝ] ℝ)
    (hint : ∀ y : E, y ∈ L → ∃ c : ℤ, F y = (c : ℝ))
    (v : E) (hvL : v ∈ L) (hv : F v = 1)
    (b : Basis I ℤ (kernelLattice L F)) (i : I) :
    (adaptedLatticeBasis L F hint v hvL hv b (Sum.inr i) : E) = ((b i : F.toLinearMap.ker) : E) := by
  simp [adaptedLatticeBasis,latticeSplitEquiv,LinearEquiv.ofBijective_apply,latticeJoin_apply]

#print axioms latticeJoin_bijective
#print axioms adaptedLatticeBasis_left
end Erdos3PrimitiveLatticeSplitting
