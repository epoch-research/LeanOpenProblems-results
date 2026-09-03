import Submission.TrackedCyclePartition
import Submission.OneMemberTransfer

/-! Restoring two triangles sharing an isolated hub within a given path budget. -/
namespace Erdos583ButterflyRestorationDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.TriangleAbsorption
open Erdos583CorePathPiecesDevelopment Erdos583ButterflyRoutesDevelopment
open Erdos583ButterflyPentagonDevelopment Erdos583OneMemberReplacementDevelopment
open Erdos583OneMemberTransferDevelopment Erdos583TrackedCyclePartitionDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma butterfly_partition_or_pentagon {V : Type*} [Fintype V] {F G : SimpleGraph V}
    (hFG : F ≤ G) (f : Fin 5 → V) (hf : Function.Injective f)
    (ha : ∀ i, G.Adj (f (baseSource i)) (f (baseTarget i)))
    (hdis : Disjoint (coreEdges baseSource baseTarget f) F.edgeSet)
    (hcover : G.edgeSet=F.edgeSet ∪ coreEdges baseSource baseTarget f)
    (hhub : f 0 ∉ F.support) (htouch : ∃ i, f i ∈ F.support)
    (D : Finset F.Subgraph) (hD : GoodDecomposition F D) :
    (∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1) ∨
    ∃ C : G.Walk (f 0) (f 0), C.IsCycle ∧ C.length=5 ∧
      ∃ E : Finset (G.deleteEdges C.toSubgraph.edgeSet).Subgraph,
        GoodDecomposition (G.deleteEdges C.toSubgraph.edgeSet) E ∧ E.card ≤ D.card := by
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
  have hnP : ¬P.Nil := by
    intro hn
    have hh := P.mem_edges_toSubgraph.mp (hKe ▸ heK)
    rw [Walk.edges_eq_nil.mpr hn] at hh
    exact List.not_mem_nil hh
  have hmiss : f 0 ∉ R.support := by
    simp only [R,Walk.support_mapLe_eq_support]
    exact fun hh ↦ hhub (path_support_subset_graph_support hP hnP _ hh)
  have hmeet : ∃ j, f j ∈ R.support := by
    refine ⟨i,?_⟩
    simp only [R,Walk.support_mapLe_eq_support]
    exact P.fst_mem_support_of_mem_edges (P.mem_edges_toSubgraph.mp (hKe ▸ heK))
  have havoid : ∀ j, s(f (baseSource j),f (baseTarget j)) ∉ R.edges := by
    intro j hj
    apply Set.disjoint_left.mp hdis
    · exact Set.mem_iUnion.mpr ⟨j,rfl⟩
    · exact K.edgeSet_subset (hRe ▸ R.mem_edges_toSubgraph.mpr hj)
  have hrest : Disjoint (coreEdges baseSource baseTarget f ∪ K.edgeSet) (F.edgeSet \ K.edgeSet) := by
    apply Set.disjoint_left.mpr
    rintro e (he|he) hh
    · exact Set.disjoint_left.mp hdis he hh.1
    · exact hh.2 he
  have htotal : G.edgeSet=(F.edgeSet \ K.edgeSet) ∪
      (coreEdges baseSource baseTarget f ∪ K.edgeSet) := by
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
  rcases butterfly_path_or_pentagon f hf ha R hR hmiss hmeet havoid with htwo | hpent
  · obtain ⟨u,v,s,t,A,B,hA,hB,hAB,hABe⟩ := htwo
    rw [hRe] at hABe
    have hrest' : Disjoint (A.toSubgraph.edgeSet ∪ B.toSubgraph.edgeSet) (F.edgeSet \ K.edgeSet) := by
      rwa [hABe]
    left
    apply replace_one_by_two hFG D hD K hKD A.toSubgraph B.toSubgraph
      ⟨_,_,A,hA,rfl⟩ ⟨_,_,B,hB,rfl⟩ hAB
      (disjoint_sup_left.mp hrest').1 (disjoint_sup_left.mp hrest').2
    rw [Set.union_assoc,hABe]
    exact htotal
  · obtain ⟨C,Q,hC,hCl,hQ,hCQ,hCQe⟩ := hpent
    rw [hRe] at hCQe
    right
    refine ⟨C,hC,hCl,?_⟩
    apply replace_one_keeping_separate D hD K hKD C.toSubgraph Q.toSubgraph
      ⟨_,_,Q,hQ,rfl⟩ hCQ
    · rwa [hCQe]
    · rwa [hCQe]

lemma failure_no_butterfly_partition {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {F G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hFG : F ≤ G) (f : Fin 5 → Fin n) (hf : Function.Injective f)
    (ha : ∀ i, G.Adj (f (baseSource i)) (f (baseTarget i)))
    (hdis : Disjoint (coreEdges baseSource baseTarget f) F.edgeSet)
    (hcover : G.edgeSet=F.edgeSet ∪ coreEdges baseSource baseTarget f)
    (hhub : f 0 ∉ F.support) (htouch : ∃ i, f i ∈ F.support)
    (D : Finset F.Subgraph) (hD : GoodDecomposition F D)
    (hcount : D.card+1 ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) : False := by
  rcases butterfly_partition_or_pentagon hFG f hf ha hdis hcover hhub htouch D hD with hpaths | hpent
  · obtain ⟨E,hE,hEc⟩ := hpaths
    exact hfail ⟨E,hE,hEc.trans hcount⟩
  · obtain ⟨C,hC,hCl,E,hE,hEc⟩ := hpent
    apply failure_no_pentagon_partition hsmall hG hfail (deleteEdges_le C.toSubgraph.edgeSet)
      C hC hCl _ _ E hE (by omega)
    · rw [edgeSet_deleteEdges]
      exact Set.disjoint_left.mpr (fun _ he hh ↦ hh.2 he)
    · rw [edgeSet_deleteEdges,Set.union_comm]
      exact (Set.diff_union_of_subset C.toSubgraph.edgeSet_subset).symm

end Erdos583ButterflyRestorationDevelopment
