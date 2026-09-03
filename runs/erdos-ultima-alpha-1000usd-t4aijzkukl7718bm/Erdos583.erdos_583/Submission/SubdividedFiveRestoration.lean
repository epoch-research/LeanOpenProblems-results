import Submission.TwoReplacementTransfer

/-! Budget-aware restoration of a subdivided K5 through a touching ordinary path. -/
namespace Erdos583SubdividedFiveRestorationDevelopment
open SimpleGraph Erdos583Work
open Erdos583SubdividedFiveFiniteDevelopment Erdos583SubdividedFiveAbsorptionDevelopment
open Erdos583TwoReplacementTransferDevelopment Erdos583TrackedCyclePartitionDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma subdivided_five_partition_to_pentagon {V : Type*} [Fintype V] {F G : SimpleGraph V}
    (hFG : F ≤ G) (f : base →g G) (hf : Function.Injective f)
    (hdis : Disjoint (Sym2.map f '' base.edgeSet) F.edgeSet)
    (hcover : G.edgeSet=F.edgeSet ∪ (Sym2.map f '' base.edgeSet))
    (htouch : ∃ i : Fin 6, f i ∈ F.support) (D : Finset F.Subgraph) (hD : GoodDecomposition F D) :
    ∃ C : G.Walk (f 0) (f 0), C.IsCycle ∧ C.length=5 ∧
      ∃ E : Finset (G.deleteEdges C.toSubgraph.edgeSet).Subgraph,
        GoodDecomposition (G.deleteEdges C.toSubgraph.edgeSet) E ∧ E.card ≤ D.card+1 := by
  classical
  obtain ⟨i,w,hiw⟩ := htouch
  have he : s(f i,w) ∈ F.edgeSet := hiw
  rw [←hD.2.2] at he
  obtain ⟨K,hKD,heK⟩ := Set.mem_iUnion₂.mp he
  obtain ⟨a,b,P,hP,hKe⟩ := hD.1 K hKD
  let R := P.mapLe hFG
  have hR : R.IsPath := hP.mapLe hFG
  have hRe : R.toSubgraph.edgeSet=K.edgeSet := by
    rw [hKe]; simp only [R,Walk.edgeSet_toSubgraph,Walk.edges_mapLe_eq_edges]
  have hRP : Disjoint (Sym2.map f '' base.edgeSet) R.toSubgraph.edgeSet := by
    rw [hRe]
    exact hdis.mono_right K.edgeSet_subset
  have hmeet : ∃ j : Fin 6, f j ∈ R.support := by
    refine ⟨i,?_⟩
    simp only [R,Walk.support_mapLe_eq_support]
    exact P.fst_mem_support_of_mem_edges (P.mem_edges_toSubgraph.mp (hKe ▸ heK))
  obtain ⟨C,hC,hCl,S,hCS,hCSe,htwo⟩ := subdivided_five_path_to_pentagon f hf R hR hRP hmeet
  obtain ⟨u,v,s,t,A,B,hA,hB,hAB,hABe⟩ := htwo
  rw [hRe] at hCSe
  have hrest : Disjoint ((Sym2.map f '' base.edgeSet) ∪ K.edgeSet) (F.edgeSet \ K.edgeSet) := by
    apply Set.disjoint_left.mpr
    rintro e (he|he) hh
    · exact Set.disjoint_left.mp hdis he hh.1
    · exact hh.2 he
  have htotal : G.edgeSet=(F.edgeSet \ K.edgeSet) ∪ ((Sym2.map f '' base.edgeSet) ∪ K.edgeSet) := by
    rw [hcover]
    ext e
    constructor
    · rintro (he|he)
      · by_cases hk : e ∈ K.edgeSet
        · exact Or.inr (Or.inr hk)
        · exact Or.inl ⟨he,hk⟩
      · exact Or.inr (Or.inl he)
    · rintro (he|he|he)
      · exact Or.inl he.1
      · exact Or.inr he
      · exact Or.inl (K.edgeSet_subset he)
  refine ⟨C,hC,hCl,?_⟩
  apply replace_one_by_two_keeping_separate D hD K hKD C.toSubgraph A.toSubgraph B.toSubgraph
    ⟨_,_,A,hA,rfl⟩ ⟨_,_,B,hB,rfl⟩ hAB
  · rwa [hABe]
  · rwa [hABe,hCSe]
  · rwa [hABe,hCSe]

lemma failure_no_subdivided_five_partition {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {F G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hFG : F ≤ G) (f : base →g G) (hf : Function.Injective f)
    (hdis : Disjoint (Sym2.map f '' base.edgeSet) F.edgeSet)
    (hcover : G.edgeSet=F.edgeSet ∪ (Sym2.map f '' base.edgeSet))
    (htouch : ∃ i : Fin 6, f i ∈ F.support) (D : Finset F.Subgraph) (hD : GoodDecomposition F D)
    (hcount : D.card+2 ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) : False := by
  obtain ⟨C,hC,hCl,E,hE,hEc⟩ := subdivided_five_partition_to_pentagon hFG f hf hdis hcover htouch D hD
  apply failure_no_pentagon_partition hsmall hG hfail (deleteEdges_le C.toSubgraph.edgeSet)
    C hC hCl _ _ E hE (by omega)
  · rw [edgeSet_deleteEdges]
    exact Set.disjoint_left.mpr (fun _ he hh ↦ hh.2 he)
  · rw [edgeSet_deleteEdges,Set.union_comm]
    exact (Set.diff_union_of_subset C.toSubgraph.edgeSet_subset).symm

lemma failure_no_subdivided_five_support_saving {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {F G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hFG : F ≤ G) (f : base →g G) (hf : Function.Injective f)
    (hdis : Disjoint (Sym2.map f '' base.edgeSet) F.edgeSet)
    (hcover : G.edgeSet=F.edgeSet ∪ (Sym2.map f '' base.edgeSet))
    (htouch : ∃ i : Fin 6, f i ∈ F.support)
    (hF : SupportConnected F) (hcard : F.support.ncard+4 ≤ n) : False := by
  obtain ⟨D,hD,hDc⟩ := LowDegreeAdjacency.smaller_orders_on_support hsmall F hF (by omega)
  apply failure_no_subdivided_five_partition hsmall hG hfail hFG f hf hdis hcover htouch D hD
  rw [BridgeGlue.ceil_half] at hDc
  simp only [Fintype.card_fin,BridgeGlue.ceil_half]
  omega

end Erdos583SubdividedFiveRestorationDevelopment
