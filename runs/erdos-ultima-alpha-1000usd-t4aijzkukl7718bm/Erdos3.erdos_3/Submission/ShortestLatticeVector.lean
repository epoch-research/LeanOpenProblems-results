import Submission.PrimitiveLatticeFunctional

/-! Shortest nonzero lattice vectors exist, and a shortest vector is primitive:
some integral dual functional takes value one on it. -/
namespace Erdos3ShortestLatticeVector
open Finset Module Erdos3LatticePhaseCoordinates Erdos3PrimitiveIntegerFrequency
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

section Minimum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

theorem exists_shortest_lattice_vector (L : Submodule ℤ E) [DiscreteTopology L]
    (hL : L ≠ ⊥) : ∃ v : E, v ∈ L ∧ v ≠ 0 ∧ ∀ w : E, w ∈ L → w ≠ 0 → ‖v‖ ≤ ‖w‖ := by
  letI : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  obtain ⟨x,hx,hx0⟩ := L.ne_bot_iff.mp hL
  have hclosed : IsClosed (L : Set E) := AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup)
  have hfinite : (Metric.closedBall (0 : E) ‖x‖ ∩ (L : Set E)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete Metric.isBounded_closedBall hclosed
  let S := hfinite.toFinset.erase 0
  have hmem (y : E) : y ∈ S ↔ y ≠ 0 ∧ ‖y‖ ≤ ‖x‖ ∧ y ∈ L := by
    simp only [S,mem_erase,Set.Finite.mem_toFinset,Set.mem_inter_iff,Metric.mem_closedBall,dist_zero_right]
    tauto
  have hS : S.Nonempty := ⟨x,(hmem x).mpr ⟨hx0,le_refl _,hx⟩⟩
  obtain ⟨v,hv,hmin⟩ := exists_min_image S (fun y ↦ ‖y‖) hS
  obtain ⟨hv0,hvx,hvL⟩ := (hmem v).mp hv
  refine ⟨v,hvL,hv0,?_⟩
  intro w hw hw0
  by_cases hwx : ‖w‖ ≤ ‖x‖
  · exact hmin w ((hmem w).mpr ⟨hw0,hwx,hw⟩)
  · exact hvx.trans (le_of_not_ge hwx)

end Minimum

section Primitive
variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A shortest vector cannot have a nontrivial positive common divisor in its
integer coordinates. Bezout then supplies the required primitive functional. -/
theorem shortest_vector_primitive_of_basis (b : Basis I ℝ E) (v : E)
    (hv : v ∈ Submodule.span ℤ (Set.range b)) (hv0 : v ≠ 0)
    (hmin : ∀ w : E, w ∈ Submodule.span ℤ (Set.range b) → w ≠ 0 → ‖v‖ ≤ ‖w‖) :
    ∃ F : E →L[ℝ] ℝ, F v = 1 ∧
      ∀ w : E, w ∈ Submodule.span ℤ (Set.range b) → ∃ c : ℤ, F w = (c : ℝ) := by
  have hcoord : ∀ i, ∃ h : ℤ, (h : ℝ) = b.repr v i := by
    intro i
    exact (b.mem_span_iff_repr_mem ℤ v).mp hv i
  choose h hh using hcoord
  have hne : ∃ i, h i ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hv0
    apply b.ext_elem
    intro i
    rw [← hh i,hn i]
    simp
  obtain ⟨g,h₀,c,hg,hdiv,hcomb,_,_⟩ := primitive_integer_frequency h hne
  let w : E := ∑ i, h₀ i • b i
  have hw : w ∈ Submodule.span ℤ (Set.range b) := by
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  have hsplit : v = (g : ℝ) • w := by
    calc
      _ = ∑ i, (b.repr v i) • b i := (b.sum_repr v).symm
      _ = ∑ i, ((g : ℝ)*(h₀ i : ℝ)) • b i := by
        apply sum_congr rfl
        intro i _
        rw [← hh i,hdiv i,Int.cast_mul,Int.cast_natCast]
      _ = _ := by
        dsimp only [w]
        rw [smul_sum]
        apply sum_congr rfl
        intro i _
        rw [← Int.cast_smul_eq_zsmul ℝ,smul_smul]
  have hw0 : w ≠ 0 := by intro hh; rw [hh,smul_zero] at hsplit; exact hv0 hsplit
  have hg1 : g = 1 := by
    have hm := hmin w hw hw0
    rw [hsplit,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg g : (0 : ℝ) ≤ g)] at hm
    have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    by_contra hh
    have hgg : (2 : ℝ) ≤ g := by exact_mod_cast (show 2 ≤ g by omega)
    nlinarith only [hm,hn,mul_le_mul_of_nonneg_right hgg hn.le]
  have hhi (i : I) : h i = h₀ i := by simpa only [hg1,Nat.cast_one,one_mul] using hdiv i
  refine ⟨dualFrequency b c,?_,fun y hy ↦ dualFrequency_integral b c y hy⟩
  rw [dualFrequency_apply]
  simp_rw [← hh,hhi]
  exact_mod_cast hcomb

/-- Basis-independent primitivity of a shortest nonzero vector in a full lattice. -/
theorem shortest_vector_primitive (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (v : E) (hv : v ∈ L) (hv0 : v ≠ 0)
    (hmin : ∀ w : E, w ∈ L → w ≠ 0 → ‖v‖ ≤ ‖w‖) :
    ∃ F : E →L[ℝ] ℝ, F v = 1 ∧ ∀ w : E, w ∈ L → ∃ c : ℤ, F w = (c : ℝ) := by
  let b := Free.chooseBasis ℤ L
  have hspan := b.ofZLatticeBasis_span ℝ
  obtain ⟨F,hF,hint⟩ := shortest_vector_primitive_of_basis (b.ofZLatticeBasis ℝ) v
    (by simpa only [hspan] using hv) hv0 (by simpa only [hspan] using hmin)
  exact ⟨F,hF,by simpa only [hspan] using hint⟩

#print axioms exists_shortest_lattice_vector
#print axioms shortest_vector_primitive
end Primitive
end Erdos3ShortestLatticeVector
