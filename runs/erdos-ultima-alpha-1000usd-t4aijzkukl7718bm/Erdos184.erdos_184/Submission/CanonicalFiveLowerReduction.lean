import Submission.CanonicalPairAdmissibility
import Submission.FourGraphFamily

/-! The canonical reduction after excluding maximum families of four cycles.
This still concerns only hypothetical nonrigid cores of optimum three. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CanonicalThreeReduction
open Erdos184Serial Critical EvenCore Rigidity MaximumCycles MaximumCoreFamilies CycleSegments
open PairJunctionCoding JunctionPairCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable local instance canonicalFiveLowerDecEq {l : ℕ} {m : Fin l → ℕ} :
    DecidableEq (Σ i, Fin (m i)) := Classical.decEq _
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma exists_admissible_canonical_kernel_ge_five (he : ∀ x, Even (G.degree x))
    (hm : EvenMinimal G) (hn : number G = 3) (hr : ¬ CycleRigid G) :
    ∃ l : ℕ, 5 ≤ l ∧ ∃ b : PairIndex l → Fin 3,
    ∃ hb : ∀ i, 2 ≤ (markers b i).card,
    ∃ o : ∀ i, Marked.Order (arity b i), Restrictions b hb o ∧ Numeric b := by
  obtain ⟨D,hD,hcard,root,C,hC,hwalk,hd,hcover,hcontact⟩ :=
    three_core_junction_family he hm hn hr
  have hfive := FourGraphFamily.three_core_maximum_ge_five hD he hm hn hr
  let l := D.card
  let e : Fin l ≃ D := (Fintype.equivFinOfCardEq (by simp [l])).symm
  let B0 : D → Set V := fun i => {x | x ∈ (C i).support}
  let B : Fin l → Set V := B0 ∘ e
  let root' : Fin l → V := root ∘ e
  let C' : ∀ i : Fin l, G.Walk (root' i) (root' i) := fun i => C (e i)
  have hBC (i : Fin l) : B i = {x | x ∈ (C' i).support} := rfl
  have htwo0 (w : Junction B0) : Nat.card {i : D // w.val ∈ B0 i} = 2 := by
    have h := junction_two_incidence hD (degree_le_four_of_nonrigid_three he hm hn hr) root C hwalk w
    simpa only [← Nat.card_eq_fintype_card,Set.mem_setOf_eq] using h
  have htwo (w : Junction B) : Nat.card {i : Fin l // w.val ∈ B i} = 2 := by
    change Nat.card {i : Fin l // w.val ∈ (B0 ∘ e) i} = 2
    rw [incidence_natCard_reindex]
    exact htwo0 (junctionReindex B0 e w)
  have hs0 (i : D) : B0 i = i.val.verts := by
    ext x
    rw [← hwalk i,Walk.mem_verts_toSubgraph]
    rfl
  have hbound (i j : Fin l) (hij : i ≠ j) : (B i ∩ B j).ncard ≤ 2 := by
    change (B0 (e i) ∩ B0 (e j)).ncard ≤ 2
    rw [hs0,hs0]
    exact maximum_decomposition_intersection_le_two D hD.1 hD.2.1 hD.2.2 _ _
      (e i).property (e j).property (fun h => hij (e.injective (Subtype.ext h)))
  have hcontacts (i : Fin l) : 2 ≤ Fintype.card (LocalJunction B i) := by
    change 2 ≤ Fintype.card (LocalJunction (B0 ∘ e) i)
    rw [localJunction_card_reindex]
    exact hcontact (e i)
  have hC' (i : Fin l) : (C' i).IsCycle := hC (e i)
  have hd' (i j : Fin l) (hij : i ≠ j) : (C' i).edges.Disjoint (C' j).edges :=
    hd (e i) (e j) (e.injective.ne hij)
  have hcover' (x y : V) (hxy : G.Adj x y) : ∃ i, s(x,y) ∈ (C' i).edges := by
    obtain ⟨i,hi⟩ := hcover x y hxy
    refine ⟨e.symm i,?_⟩
    change s(x,y) ∈ (C (e (e.symm i))).edges
    rwa [e.apply_symm_apply]
  have hwalk' : Function.Injective (fun i => (C' i).toSubgraph) := by
    intro i j h
    change (C (e i)).toSubgraph = (C (e j)).toSubgraph at h
    rw [hwalk,hwalk] at h
    exact e.injective (Subtype.ext h)
  have hmem' (i : Fin l) : (C' i).toSubgraph ∈ D := by
    change (C (e i)).toSubgraph ∈ D
    rw [hwalk]
    exact (e i).property
  obtain ⟨o,F,hvertex,hsrc,hdst,hpiece,hcov⟩ :=
    CanonicalPairLayout.exists_ordered_family B htwo hbound hcontacts root' C' hBC hC' hd' hcover'
  have hh := IndexedKernelRestrictions.restrictions hD hcard he hm hn hr root' C' hC' hwalk' hmem'
    hd' F hpiece hcov
  rw [hsrc,hdst] at hh
  refine ⟨l,by dsimp [l]; omega,counts B htwo hbound,
    marker_card_lower B htwo hbound hcontacts,o,?_⟩
  refine ⟨?_,?_⟩
  · change MinimalCore _ _ 3 ∧ ¬ Rigid _ _ 3 ∧ _ ∧ _
    refine ⟨?_,?_,?_,?_⟩
    · exact (recursive_minimal_iff B htwo hbound hcontacts o 3).mp hh.1
    · intro hrig
      apply hh.2.1
      exact (NormalizedKernel.rigid_univ_iff (actualPlace B htwo hbound hcontacts) o 3).mpr
        ((normalized_rigid_iff B htwo hbound hcontacts o 3).mpr hrig)
    · intro A
      apply (normalized_upper_iff B htwo hbound hcontacts o A A.card).mp
      exact (NormalizedKernel.upper_colors_iff (actualPlace B htwo hbound hcontacts) o A A.card).mp
        (hh.2.2.1 A)
    · intro A hA
      apply (normalized_exists_iff B htwo hbound hcontacts o A 2).mp
      exact (NormalizedKernel.exists_colors_iff (actualPlace B htwo hbound hcontacts) o A 2).mp
        (hh.2.2.2 A hA)

  · exact counts_numeric B htwo hbound hD hcard he hm hn hr (fun i => (e i).val)
      (fun i j hij => e.injective (Subtype.ext hij)) (fun i => (e i).property)
      (fun i => hs0 (e i))

#print axioms exists_admissible_canonical_kernel_ge_five
end Erdos184Work.CanonicalThreeReduction
