import Submission.SixRepresentativeKernels
import Submission.CanonicalLocalExtraction
import Submission.AllowedFiveCounts

/-! Conditional six-color conclusions for actual maximum cycle families.
The local classification does not imply an arbitrary-core bound. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.SixGraphFamily
open Critical MaximumCycles MaximumCoreFamilies CycleSegments
open PairJunctionCoding JunctionPairCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel
open Erdos184Serial LabelKernel CanonicalThreeReduction
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable local instance sixGraphDecEq {I : Type*} {m : I → ℕ} :
    DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma number_and_contacts {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (hcD : D.card = 6) (hdeg : ∀ x, G.degree x ≤ 4)
    (hthree : ∀ A ⊆ D, A.card = 3 → number (subfamilyGraph A) ≤ 2)
    (hpos : ∀ H ∈ D, ∀ K ∈ D, H ≠ K → 0 < (H.verts ∩ K.verts).ncard) :
    number G ≤ 2 ∧ ∃ k : Fin 5, k ∈ SixRepresentativeKernels.allowed ∧
      ∃ e : Fin 6 ≃ D, ∀ i j, i ≠ j →
        ((e i).val.verts ∩ (e j).val.verts).ncard =
          PureSixDoublePatterns.between (PureSixDoublePatterns.representative k) i j := by
  let e0 : Fin 6 ≃ D := (Fintype.equivFinOfCardEq (by simpa using hcD)).symm
  let H : Fin 6 → G.Subgraph := fun i => (e0 i).val
  have hH : Function.Injective H := Subtype.val_injective.comp e0.injective
  have hmemH (i : Fin 6) : H i ∈ D := (e0 i).property
  obtain ⟨k,p,hp⟩ := PureSixDoublePatterns.classified_nat
    (fun i j => ((H i).verts ∩ (H j).verts).ncard)
    (by intro i j; exact congrArg Set.ncard (Set.inter_comm (H i).verts (H j).verts))
    (fun i j hij => hpos _ (hmemH i) _ (hmemH j) (hH.ne hij))
    (fun i j hij => maximum_decomposition_intersection_le_two D hD.1 hD.2.1 hD.2.2
      _ _ (hmemH i) (hmemH j) (hH.ne hij)) (by
        intro v
        exact AllowedFiveCounts.pattern_count_le _
          (FiveSubfamilyPatterns.allowed_pattern hD hdeg hthree hpos
            (H ∘ PureSixDoublePatterns.omitColor v)
            (hH.comp (PureSixDoublePatterns.omitColor_injective v))
            (fun i => hmemH (PureSixDoublePatterns.omitColor v i))))
  let e : Fin 6 ≃ D := p.trans e0
  obtain ⟨root,C,hC,hwalk⟩ := walks_of_cycle_family D hD.1
  let B0 : D → Set V := fun i => {x | x ∈ (C i).support}
  let B : Fin 6 → Set V := B0 ∘ e
  let root' : Fin 6 → V := root ∘ e
  let C' : ∀ i : Fin 6, G.Walk (root' i) (root' i) := fun i => C (e i)
  have hBC (i : Fin 6) : B i = {x | x ∈ (C' i).support} := rfl
  have hs0 (i : D) : B0 i = i.val.verts := by
    ext x
    rw [← hwalk i,Walk.mem_verts_toSubgraph]
    rfl
  have htwo (w : Junction B) : Nat.card {i : Fin 6 // w.val ∈ B i} = 2 := by
    change Nat.card {i : Fin 6 // w.val ∈ (B0 ∘ e) i} = 2
    rw [incidence_natCard_reindex]
    simpa only [← Nat.card_eq_fintype_card,Set.mem_setOf_eq] using
      junction_two_incidence hD hdeg root C hwalk (junctionReindex B0 e w)
  have hbound (i j : Fin 6) (hij : i ≠ j) : (B i ∩ B j).ncard ≤ 2 := by
    change (B0 (e i) ∩ B0 (e j)).ncard ≤ 2
    rw [hs0,hs0]
    exact maximum_decomposition_intersection_le_two D hD.1 hD.2.1 hD.2.2 _ _
      (e i).property (e j).property (fun he => hij (e.injective (Subtype.ext he)))
  have hcontacts (i : Fin 6) : 2 ≤ Fintype.card (LocalJunction B i) := by
    change 2 ≤ Fintype.card (LocalJunction (B0 ∘ e) i)
    rw [localJunction_card_reindex]
    rw [junction_card_of_family D root C hwalk]
    exact contacts_of_triple_bounds hD.1 hD.2.1.1 (by omega) hthree _ (e i).property
  have heq : counts B htwo hbound = SixCanonicalCounts.counts k := by
    funext q
    apply Fin.ext
    rw [counts_val]
    change (B0 (e q.val.1) ∩ B0 (e q.val.2)).ncard = _
    rw [hs0,hs0]
    have hh := hp q.val.1 q.val.2 (ne_of_lt q.property)
    simpa only [e,Equiv.trans_apply,H,SixCanonicalCounts.counts,
      PureSixDoublePatterns.between,if_neg (ne_of_lt q.property)] using hh
  have hC' (i : Fin 6) : (C' i).IsCycle := hC (e i)
  have hd' (i j : Fin 6) (hij : i ≠ j) : (C' i).edges.Disjoint (C' j).edges := by
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
  have hmem' (i : Fin 6) : (C' i).toSubgraph ∈ D := by
    change (C (e i)).toSubgraph ∈ D
    rw [hwalk]
    exact (e i).property
  have hthree' (A : Finset (Fin 6)) (hA : A.card = 3) :
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
  have htwoK := SixRepresentativeKernels.exists_two_of_eq k (counts B htwo hbound)
    (marker_card_lower B htwo hbound hcontacts) heq o hlocal
  have hn := CanonicalLocalExtraction.number_le_of_two B htwo hbound hcontacts
    root' C' hC' hd' o F hsrc hdst hpiece hcov htwoK
  have himage : Finset.univ.image (fun i => (C' i).toSubgraph) = D := by
    ext K
    constructor
    · intro hK
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hK
      exact hmem' i
    · intro hK
      let j : D := ⟨K,hK⟩
      refine Finset.mem_image.mpr ⟨e.symm j,Finset.mem_univ _,?_⟩
      change (C (e (e.symm j))).toSubgraph = K
      rw [e.apply_symm_apply,hwalk]
  have hg : subfamilyGraph D = G :=
    SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hD.2.1.2)
  have hnG : number G ≤ 2 := by rwa [himage,hg] at hn
  have hk := SixRepresentativeKernels.allowed_of_eq k (counts B htwo hbound)
    (marker_card_lower B htwo hbound hcontacts) heq o hlocal
  refine ⟨hnG,k,hk,e,?_⟩
  intro i j hij
  exact hp i j hij

lemma number_le_two {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (hcD : D.card = 6) (hdeg : ∀ x, G.degree x ≤ 4)
    (hthree : ∀ A ⊆ D, A.card = 3 → number (subfamilyGraph A) ≤ 2)
    (hpos : ∀ H ∈ D, ∀ K ∈ D, H ≠ K → 0 < (H.verts ∩ K.verts).ncard) :
    number G ≤ 2 := (number_and_contacts hD hcD hdeg hthree hpos).1

lemma subfamily_number_le_two {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (hdeg : ∀ x, G.degree x ≤ 4)
    (hthree : ∀ A ⊆ D, A.card = 3 → number (subfamilyGraph A) ≤ 2)
    (hpos : ∀ H ∈ D, ∀ K ∈ D, H ≠ K → 0 < (H.verts ∩ K.verts).ncard)
    (A : Finset G.Subgraph) (hAD : A ⊆ D) (hcA : A.card = 6) :
    number (subfamilyGraph A) ≤ 2 := by
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
  apply number_le_two hmax (hEA.trans hcA)
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

lemma three_core_maximum_ge_seven {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (he : ∀ v, Even (G.degree v)) (hm : EvenCore.EvenMinimal G)
    (hn : number G = 3) (hr : ¬ Rigidity.CycleRigid G) : 7 ≤ D.card := by
  have hge := FiveGraphFamily.three_core_maximum_ge_six hD he hm hn hr
  by_contra hsmall
  have hcD : D.card = 6 := by omega
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
  have hb := number_le_two hD hcD hdeg hthree hpos
  omega

#print axioms three_core_maximum_ge_seven
#print axioms number_and_contacts
#print axioms subfamily_number_le_two
#print axioms number_le_two
end Erdos184Work.SixGraphFamily
