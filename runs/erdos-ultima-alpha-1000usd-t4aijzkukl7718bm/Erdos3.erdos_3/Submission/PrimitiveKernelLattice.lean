import Submission.KernelProjectionEstimates

/-! The kernel of a primitive integral dual functional contains a full lattice
of one lower real dimension. Integrality, discreteness, and full span are
proved explicitly. -/
namespace Erdos3PrimitiveKernelLattice
open Module Erdos3KernelProjectionEstimates
set_option maxHeartbeats 3000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def kernelLattice (L : Submodule ℤ E) (F : E →L[ℝ] ℝ) :
    Submodule ℤ F.toLinearMap.ker :=
  ZLattice.comap ℝ L F.toLinearMap.ker.subtype

lemma mem_kernelLattice (L : Submodule ℤ E) (F : E →L[ℝ] ℝ) (x : F.toLinearMap.ker) :
    x ∈ kernelLattice L F ↔ (x : E) ∈ L := Iff.rfl

instance kernelLattice_discrete (L : Submodule ℤ E) [DiscreteTopology L] (F : E →L[ℝ] ℝ) :
    DiscreteTopology (kernelLattice L F) :=
  ZLattice.comap_discreteTopology ℝ L continuous_subtype_val Subtype.val_injective

/-- Primitivity supplies a lattice point v with F(v)=1. Subtracting F(y)*v
therefore projects every lattice point integrally into the kernel. -/
theorem kernelLattice_span_top (L : Submodule ℤ E) (F : E →L[ℝ] ℝ)
    (hspan : Submodule.span ℝ (L : Set E) = ⊤)
    (hint : ∀ y : E, y ∈ L → ∃ c : ℤ, F y = (c : ℝ))
    (v : E) (hvL : v ∈ L) (hv : F v = 1) :
    Submodule.span ℝ (kernelLattice L F : Set F.toLinearMap.ker) = ⊤ := by
  let P := projectToKernel F v hv
  have hsurj : Function.Surjective P := by
    intro x
    refine ⟨(x : E),?_⟩
    apply Subtype.ext
    exact projectionAlong_eq_self F v x x.property
  have himage : P '' (L : Set E) ⊆ (kernelLattice L F : Set F.toLinearMap.ker) := by
    rintro x ⟨y,hy,rfl⟩
    obtain ⟨c,hc⟩ := hint y hy
    change y-F y • v ∈ L
    rw [hc,Int.cast_smul_eq_zsmul ℝ]
    exact L.sub_mem hy (L.smul_mem c hvL)
  apply le_antisymm le_top
  calc
    _ = Submodule.map P.toLinearMap (Submodule.span ℝ (L : Set E)) := by
      rw [hspan,Submodule.map_top,LinearMap.range_eq_top.mpr hsurj]
    _ = Submodule.span ℝ (P '' (L : Set E)) := Submodule.map_span P.toLinearMap _
    _ ≤ _ := Submodule.span_mono himage

/-- The descended integer lattice is genuine, not just a subgroup of the
correct ambient hyperplane. -/
theorem kernelLattice_isZLattice (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (F : E →L[ℝ] ℝ) (hint : ∀ y : E, y ∈ L → ∃ c : ℤ, F y = (c : ℝ))
    (v : E) (hvL : v ∈ L) (hv : F v = 1) : IsZLattice ℝ (kernelLattice L F) :=
  ⟨kernelLattice_span_top L F IsZLattice.span_top hint v hvL hv⟩

lemma kernel_finrank [FiniteDimensional ℝ E] (F : E →L[ℝ] ℝ) (v : E) (hv : F v = 1) :
    finrank ℝ F.toLinearMap.ker + 1 = finrank ℝ E := by
  have hsurj : Function.Surjective F := by
    intro r
    refine ⟨r • v,?_⟩
    rw [map_smul,hv,smul_eq_mul,mul_one]
  have hh := F.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj] at hh
  simpa only [finrank_top,finrank_self,Nat.add_comm] using hh

#print axioms kernelLattice_isZLattice
#print axioms kernel_finrank
end Erdos3PrimitiveKernelLattice
