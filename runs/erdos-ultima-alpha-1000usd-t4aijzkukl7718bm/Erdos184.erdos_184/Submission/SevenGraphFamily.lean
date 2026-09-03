import Submission.SevenKernelExclusion
import Submission.SixContactUniformity
import Submission.CanonicalLocalExtraction

/-! Conditional seven-color conclusions for actual maximum cycle families.
The local classification does not imply an arbitrary-core bound. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.SevenGraphFamily
open Critical MaximumCycles MaximumCoreFamilies CycleSegments
open PairJunctionCoding JunctionPairCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel
open Erdos184Serial LabelKernel CanonicalThreeReduction
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable local instance sevenGraphDecEq {I : Type*} {m : I → ℕ} :
    DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma not_localBounds_of_eq (b' : PairIndex 7 → Fin 3)
    (hb' : ∀ i, 2 ≤ (markers b' i).card) (he : b' = SevenCanonicalCounts.counts 0)
    (o' : ∀ i, Marked.Order (arity b' i)) : ¬ LocalBounds b' hb' o' := by
  subst b'
  exact SevenKernelExclusion.not_localBounds o'

lemma not_single_family {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (hcD : D.card = 7) (hdeg : ∀ x, G.degree x ≤ 4)
    (hthree : ∀ A ⊆ D, A.card = 3 → number (subfamilyGraph A) ≤ 2)
    (hsingle : ∀ H ∈ D, ∀ K ∈ D, H ≠ K → (H.verts ∩ K.verts).ncard = 1) : False := by
  let e : Fin 7 ≃ D := (Fintype.equivFinOfCardEq (by simpa using hcD)).symm
  obtain ⟨root,C,hC,hwalk⟩ := walks_of_cycle_family D hD.1
  let B0 : D → Set V := fun i => {x | x ∈ (C i).support}
  let B : Fin 7 → Set V := B0 ∘ e
  let root' : Fin 7 → V := root ∘ e
  let C' : ∀ i : Fin 7, G.Walk (root' i) (root' i) := fun i => C (e i)
  have hBC (i : Fin 7) : B i = {x | x ∈ (C' i).support} := rfl
  have hs0 (i : D) : B0 i = i.val.verts := by
    ext x
    rw [← hwalk i,Walk.mem_verts_toSubgraph]
    rfl
  have htwo (w : Junction B) : Nat.card {i : Fin 7 // w.val ∈ B i} = 2 := by
    change Nat.card {i : Fin 7 // w.val ∈ (B0 ∘ e) i} = 2
    rw [incidence_natCard_reindex]
    simpa only [← Nat.card_eq_fintype_card,Set.mem_setOf_eq] using
      junction_two_incidence hD hdeg root C hwalk (junctionReindex B0 e w)
  have hbound (i j : Fin 7) (hij : i ≠ j) : (B i ∩ B j).ncard ≤ 2 := by
    change (B0 (e i) ∩ B0 (e j)).ncard ≤ 2
    rw [hs0,hs0]
    exact maximum_decomposition_intersection_le_two D hD.1 hD.2.1 hD.2.2 _ _
      (e i).property (e j).property (fun he => hij (e.injective (Subtype.ext he)))
  have hcontacts (i : Fin 7) : 2 ≤ Fintype.card (LocalJunction B i) := by
    change 2 ≤ Fintype.card (LocalJunction (B0 ∘ e) i)
    rw [localJunction_card_reindex]
    rw [junction_card_of_family D root C hwalk]
    exact contacts_of_triple_bounds hD.1 hD.2.1.1 (by omega) hthree _ (e i).property
  have heq : counts B htwo hbound = SevenCanonicalCounts.counts 0 := by
    funext p
    apply Fin.ext
    rw [counts_val]
    change (B0 (e p.val.1) ∩ B0 (e p.val.2)).ncard = 1
    rw [hs0,hs0]
    exact hsingle _ (e p.val.1).property _ (e p.val.2).property (by
      intro hh
      exact (ne_of_lt p.property) (e.injective (Subtype.ext hh)))
  have hC' (i : Fin 7) : (C' i).IsCycle := hC (e i)
  have hd' (i j : Fin 7) (hij : i ≠ j) : (C' i).edges.Disjoint (C' j).edges := by
    apply List.disjoint_left.mpr
    intro f hfi hfj
    have hi : f ∈ (e i).val.edgeSet := by
      rw [← hwalk (e i)]
      exact (C (e i)).mem_edges_toSubgraph.mpr hfi
    have hj : f ∈ (e j).val.edgeSet := by
      rw [← hwalk (e j)]
      exact (C (e j)).mem_edges_toSubgraph.mpr hfj
    exact Set.disjoint_left.mp (hD.2.1.1 (e i).property (e j).property
      (fun hh => hij (e.injective (Subtype.ext hh)))) hi hj
  have hcover' (x y : V) (hxy : G.Adj x y) : ∃ i, s(x,y) ∈ (C' i).edges := by
    have heG : s(x,y) ∈ G.edgeSet := hxy
    rw [← hD.2.1.2] at heG
    obtain ⟨K,hK,heK⟩ := Set.mem_iUnion₂.mp heG
    let j : D := ⟨K,hK⟩
    refine ⟨e.symm j,?_⟩
    change s(x,y) ∈ (C (e (e.symm j))).edges
    rw [e.apply_symm_apply]
    apply (C j).mem_edges_toSubgraph.mp
    rwa [hwalk]
  have hwalk' : Function.Injective (fun i => (C' i).toSubgraph) := by
    intro i j hij
    change (C (e i)).toSubgraph = (C (e j)).toSubgraph at hij
    rw [hwalk,hwalk] at hij
    exact e.injective (Subtype.ext hij)
  have hmem' (i : Fin 7) : (C' i).toSubgraph ∈ D := by
    change (C (e i)).toSubgraph ∈ D
    rw [hwalk]
    exact (e i).property
  have hthree' (A : Finset (Fin 7)) (hA : A.card = 3) :
      number (subfamilyGraph (A.image (fun i => (C' i).toSubgraph))) ≤ 2 := by
    apply hthree
    · intro K hK
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hK
      exact hmem' i
    · rwa [Finset.card_image_of_injective _ hwalk']
  obtain ⟨o,F,hvertex,hsrc,hdst,hpiece,hcov⟩ :=
    CanonicalPairLayout.exists_ordered_family B htwo hbound hcontacts root' C' hBC hC' hd' hcover'
  have hlocal := CanonicalLocalExtraction.localBounds_of_family B htwo hbound hcontacts
    root' C' hC' hd' o F hsrc hdst hpiece hcov hD hwalk' hmem' hthree'
  exact not_localBounds_of_eq (counts B htwo hbound)
    (marker_card_lower B htwo hbound hcontacts) heq o hlocal

lemma not_family {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (hcD : D.card = 7) (hdeg : ∀ x, G.degree x ≤ 4)
    (hthree : ∀ A ⊆ D, A.card = 3 → number (subfamilyGraph A) ≤ 2)
    (hpos : ∀ H ∈ D, ∀ K ∈ D, H ≠ K → 0 < (H.verts ∩ K.verts).ncard) : False :=
  not_single_family hD hcD hdeg hthree
    (SixContactUniformity.contacts_eq_one_of_ge_six hD (by omega) hdeg hthree hpos)

lemma not_subfamily {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (hdeg : ∀ x, G.degree x ≤ 4)
    (hthree : ∀ A ⊆ D, A.card = 3 → number (subfamilyGraph A) ≤ 2)
    (hpos : ∀ H ∈ D, ∀ K ∈ D, H ≠ K → 0 < (H.verts ∩ K.verts).ncard)
    (A : Finset G.Subgraph) (hAD : A ⊆ D) (hcA : A.card = 7) :
    False := by
  let hcov := (subfamilyGraph_edges A).symm
  let E := Subfamilies.lowerFamily A hcov
  have hEA : E.card = A.card := Subfamilies.lowerFamily_card A hcov
  have hcyc : ∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hD.1 i.val (hAD i.property)
  have hdec : IsDecomposition (subfamilyGraph A) E :=
    Subfamilies.lowerFamily_decomposition A hcov
      (fun H hH K hK hne => hD.2.1.1 (hAD hH) (hAD hK) hne)
  have hmax : IsMaximum (subfamilyGraph A) E := ⟨hcyc,hdec,by
    intro T hT hdT
    rw [hEA]
    exact hD.subfamily_bound A hAD T hT hdT⟩
  apply not_family hmax (hEA.trans hcA)
  · intro x
    exact (SimpleGraph.degree_le_of_le (v := x) (subfamilyGraph_le A)).trans (hdeg x)
  · intro T hTE hcT
    obtain ⟨B,hBA,hcard,hgraph⟩ := FourGraphFamily.lower_subfamily A hcov T hTE
    rw [← hgraph]
    exact hthree B (hBA.trans hAD) (hcard.trans hcT)

  · intro H hH K hK hne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hK
    exact hpos i.val (hAD i.property) j.val (hAD j.property) (by
      intro he
      exact hne (congrArg (Subfamilies.lowerPiece A hcov) (Subtype.ext he)))

lemma not_large_family {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (hcD : 7 ≤ D.card) (hdeg : ∀ x, G.degree x ≤ 4)
    (hthree : ∀ A ⊆ D, A.card = 3 → number (subfamilyGraph A) ≤ 2)
    (hpos : ∀ H ∈ D, ∀ K ∈ D, H ≠ K → 0 < (H.verts ∩ K.verts).ncard) : False := by
  obtain ⟨A,hAD,hA⟩ := Finset.exists_subset_card_eq hcD
  exact not_subfamily hD hdeg hthree hpos A hAD hA

lemma three_core_rigid (he : ∀ v, Even (G.degree v)) (hm : EvenCore.EvenMinimal G)
    (hn : number G = 3) : Rigidity.CycleRigid G := by
  by_contra hr
  obtain ⟨D,hD⟩ := exists_maximum G he
  have hge := SixGraphFamily.three_core_maximum_ge_seven hD he hm hn hr
  have hdeg := degree_le_four_of_nonrigid_three he hm hn hr
  have hthree : ∀ A ⊆ D, A.card = 3 → number (subfamilyGraph A) ≤ 2 := by
    intro A hAD hcA
    have hs : A ⊂ D := Finset.ssubset_iff_subset_ne.mpr ⟨hAD,by
      intro hh
      have hc := congrArg Finset.card hh
      omega⟩
    have hlt := proper_subfamily_number_lt hD.1 hD.2.1 hm A hs
    rw [hn] at hlt
    omega
  have hpos : ∀ H ∈ D, ∀ K ∈ D, H ≠ K → 0 < (H.verts ∩ K.verts).ncard := by
    intro H hH K hK hne
    exact FourSubfamilyPatterns.core_pair_contact_pos hD he hm hn hr ⟨H,hH⟩ ⟨K,hK⟩
      (fun hh => hne (congrArg Subtype.val hh))
  exact not_large_family hD hge hdeg hthree hpos

#print axioms not_single_family
#print axioms not_large_family
#print axioms three_core_rigid
end Erdos184Work.SevenGraphFamily
