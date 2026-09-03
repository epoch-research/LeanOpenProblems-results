import Submission.JunctionLayout

/-! Extraction of a junction kernel for a hypothetical nonrigid core of
optimum three. The finite exclusion of the resulting kernels is not assumed. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.MaximumCoreFamilies
open Critical MaximumCycles CycleContactLower CycleSegments
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma contacts_of_triple_bounds {D : Finset G.Subgraph}
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet))
    (hc : 3 ≤ D.card)
    (hthree : ∀ A ⊆ D, A.card = 3 → number (subfamilyGraph A) ≤ 2)
    (H : G.Subgraph) (hH : H ∈ D) :
    2 ≤ (H.verts ∩ vertexUnion (D.erase H)).ncard := by
  obtain ⟨A,hHA,hAD,hAc⟩ := Finset.exists_subsuperset_card_eq
    (Finset.singleton_subset_iff.mpr hH) (by simp : ({H} : Finset G.Subgraph).card ≤ 3) hc
  have hHA' : H ∈ A := hHA (Finset.mem_singleton_self _)
  have hC := two_contacts_of_number_le_two A (fun K hK => hD K (hAD hK))
    (fun K hK L hL hn => hd (hAD hK) (hAD hL) hn) hAc.ge (hthree A hAD hAc) H hHA'
  apply hC.trans (Set.ncard_mono ?_)
  rintro x ⟨hxH,hx⟩
  obtain ⟨K,hK⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hKA,hxK⟩ := Set.mem_iUnion.mp hK
  refine ⟨hxH,Set.mem_iUnion.mpr ⟨K,Set.mem_iUnion.mpr ⟨?_,hxK⟩⟩⟩
  exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hKA).1,hAD (Finset.mem_of_mem_erase hKA)⟩

lemma walks_of_cycle_family (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    ∃ root : D → V, ∃ C : ∀ i, G.Walk (root i) (root i),
      (∀ i, (C i).IsCycle) ∧ ∀ i, (C i).toSubgraph = i.val := by
  have hw (i : D) : ∃ u, ∃ p : G.Walk u u, p.IsCycle ∧ p.toSubgraph = i.val := by
    obtain ⟨v⟩ := (hD i.val i.property).1.nonempty
    obtain ⟨p,hp,he⟩ := LongRing.regular_cycle_walk_at i.val
      (hD i.val i.property).1 (hD i.val i.property).2 v.val v.property
    exact ⟨v.val,p,hp,he⟩
  choose root C hC he using hw
  exact ⟨root,C,hC,he⟩

lemma junction_card_of_family (D : Finset G.Subgraph)
    (root : D → V) (C : ∀ i, G.Walk (root i) (root i))
    (he : ∀ i, (C i).toSubgraph = i.val) (i : D) :
    Fintype.card (LocalJunction (fun j => {x | x ∈ (C j).support}) i) =
      (i.val.verts ∩ vertexUnion (D.erase i.val)).ncard := by
  have hs (i : D) (x : V) : x ∈ (C i).support ↔ x ∈ i.val.verts := by
    rw [← Walk.mem_verts_toSubgraph,he i]
  have hset : {x | x ∈ (C i).support ∧ ∃ j, j ≠ i ∧ x ∈ (C j).support} =
      i.val.verts ∩ vertexUnion (D.erase i.val) := by
    ext x
    constructor
    · rintro ⟨hxi,j,hji,hxj⟩
      refine ⟨(hs i x).mp hxi,Set.mem_iUnion.mpr ⟨j.val,Set.mem_iUnion.mpr ⟨?_,(hs j x).mp hxj⟩⟩⟩
      exact Finset.mem_erase.mpr ⟨fun h => hji (Subtype.ext h),j.property⟩
    · rintro ⟨hxi,hx⟩
      obtain ⟨H,hH⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hHD,hxH⟩ := Set.mem_iUnion.mp hH
      refine ⟨(hs i x).mpr hxi,⟨H,Finset.mem_of_mem_erase hHD⟩,?_,?_⟩
      · intro hij
        exact (Finset.mem_erase.mp hHD).1 (congrArg Subtype.val hij)
      · exact (hs _ x).mpr hxH
  rw [Fintype.card_congr (localJunctionEquiv (fun j => {x | x ∈ (C j).support}) i)]
  rw [← hset,Set.ncard_eq_toFinset_card',Set.toFinset_card]
  simp only [← Nat.card_eq_fintype_card,Set.mem_setOf_eq]
  rfl

lemma three_core_junction_family (he : ∀ x, Even (G.degree x))
    (hm : EvenCore.EvenMinimal G) (hn : number G = 3) (hr : ¬ Rigidity.CycleRigid G) :
    ∃ D : Finset G.Subgraph, IsMaximum G D ∧ 3 < D.card ∧
    ∃ root : D → V, ∃ C : ∀ i, G.Walk (root i) (root i),
      (∀ i, (C i).IsCycle) ∧ (∀ i, (C i).toSubgraph = i.val) ∧
      (∀ i j, i ≠ j → (C i).edges.Disjoint (C j).edges) ∧
      (∀ x y, G.Adj x y → ∃ i, s(x,y) ∈ (C i).edges) ∧
      (∀ i, 2 ≤ Fintype.card (LocalJunction (fun j => {x | x ∈ (C j).support}) i)) := by
  obtain ⟨D,hD,hcard,_,_,hthree⟩ := three_core_maximum_family he hm hn hr
  obtain ⟨root,C,hC,hpiece⟩ := walks_of_cycle_family D hD.1
  refine ⟨D,hD,hcard,root,C,hC,hpiece,?_,?_,?_⟩
  · intro i j hij
    apply List.disjoint_left.mpr
    intro e hei hej
    apply Set.disjoint_left.mp (hD.2.1.1 i.property j.property (fun h => hij (Subtype.ext h)))
    · rw [← hpiece i]
      exact (C i).mem_edges_toSubgraph.mpr hei
    · rw [← hpiece j]
      exact (C j).mem_edges_toSubgraph.mpr hej
  · intro x y hxy
    have heG : s(x,y) ∈ G.edgeSet := hxy
    rw [← hD.2.1.2] at heG
    obtain ⟨H,hH⟩ := Set.mem_iUnion.mp heG
    obtain ⟨hHD,heH⟩ := Set.mem_iUnion.mp hH
    refine ⟨⟨H,hHD⟩,(C ⟨H,hHD⟩).mem_edges_toSubgraph.mp ?_⟩
    rwa [hpiece]
  · intro i
    rw [junction_card_of_family D root C hpiece i]
    exact contacts_of_triple_bounds hD.1 hD.2.1.1 hcard.le hthree i.val i.property

#print axioms three_core_junction_family
end Erdos184Work.MaximumCoreFamilies
