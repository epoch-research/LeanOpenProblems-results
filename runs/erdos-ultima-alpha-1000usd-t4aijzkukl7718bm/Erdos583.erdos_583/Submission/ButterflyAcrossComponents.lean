import Submission.TwoMemberReplacement

/-! A butterfly joining two reduced components can be restored without an extra path. -/
namespace Erdos583ButterflyAcrossComponentsDevelopment
open SimpleGraph Erdos583Work
open Erdos583CorePathPiecesDevelopment Erdos583ButterflyRoutesDevelopment
open Erdos583ButterflyTwoPathsDevelopment Erdos583TwoMemberReplacementDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma restore_butterfly_across_components {V : Type*} [Fintype V] {F G : SimpleGraph V}
    (hFG : F ≤ G) (f : Fin 5 → V) (hf : Function.Injective f)
    (ha : ∀ i, G.Adj (f (baseSource i)) (f (baseTarget i)))
    (hdis : Disjoint (coreEdges baseSource baseTarget f) F.edgeSet)
    (hcover : G.edgeSet=F.edgeSet ∪ coreEdges baseSource baseTarget f)
    (hhub : f 0 ∉ F.support) (hx : f 1 ∈ F.support) (hz : f 3 ∈ F.support)
    (hnon : ¬F.Reachable (f 1) (f 3))
    (D : Finset F.Subgraph) (hD : GoodDecomposition F D) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card := by
  classical
  obtain ⟨a,b,P,hP,hnP,hxP,hPD⟩ := hD.path_through_support hx
  obtain ⟨c,d,Q,hQ,hnQ,hzQ,hQD⟩ := hD.path_through_support hz
  have hPQ : ∀ v ∈ P.support, v ∉ Q.support := by
    intro v hvP hvQ
    apply hnon
    exact ((P.takeUntil (f 1) hxP).reachable.symm.trans (P.takeUntil v hvP).reachable).trans
      ((Q.takeUntil v hvQ).reachable.symm.trans (Q.takeUntil (f 3) hzQ).reachable)
  have hne : P.toSubgraph ≠ Q.toSubgraph := by
    intro he
    exact hPQ (f 1) hxP (Q.mem_verts_toSubgraph.mp (he ▸ P.mem_verts_toSubgraph.mpr hxP))
  have hrP : f 0 ∉ P.support := fun hh ↦ hhub (path_support_subset_graph_support hP hnP _ hh)
  have hrQ : f 0 ∉ Q.support := fun hh ↦ hhub (path_support_subset_graph_support hQ hnQ _ hh)
  let P' := P.mapLe hFG
  let Q' := Q.mapLe hFG
  have hP'e : P'.toSubgraph.edgeSet=P.toSubgraph.edgeSet := by
    simp only [P',Walk.edgeSet_toSubgraph,Walk.edges_mapLe_eq_edges]
  have hQ'e : Q'.toSubgraph.edgeSet=Q.toSubgraph.edgeSet := by
    simp only [Q',Walk.edgeSet_toSubgraph,Walk.edges_mapLe_eq_edges]
  obtain ⟨u,v,s,t,A,B,hA,hB,hAB,hABe⟩ := butterfly_two_disjoint_paths f hf ha P' Q'
    (hP.mapLe hFG) (hQ.mapLe hFG)
    (by simpa only [P',Q',Walk.support_mapLe_eq_support] using hPQ)
    (by simpa only [P',Walk.support_mapLe_eq_support] using hrP)
    (by simpa only [Q',Walk.support_mapLe_eq_support] using hrQ)
    (by simpa only [P',Walk.support_mapLe_eq_support] using hxP)
    (by simpa only [Q',Walk.support_mapLe_eq_support] using hzQ)
    (by
      intro e he hh
      rw [hP'e] at hh
      exact Set.disjoint_left.mp hdis he (P.toSubgraph.edgeSet_subset hh))
    (by
      intro e he hh
      rw [hQ'e] at hh
      exact Set.disjoint_left.mp hdis he (Q.toSubgraph.edgeSet_subset hh))
  rw [hP'e,hQ'e] at hABe
  apply replace_two_by_two hFG D hD P.toSubgraph Q.toSubgraph hPD hQD hne
    A.toSubgraph B.toSubgraph ⟨_,_,A,hA,rfl⟩ ⟨_,_,B,hB,rfl⟩ hAB
  · rw [hABe]
    apply Set.disjoint_left.mpr
    rintro e (he|he) hh
    · exact Set.disjoint_left.mp hdis he hh.1
    · exact hh.2 he
  · rw [hABe,hcover]
    ext e
    constructor
    · rintro (he|he)
      · by_cases hpq : e ∈ P.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet
        · exact Or.inr (Or.inr hpq)
        · exact Or.inl ⟨he,hpq⟩
      · exact Or.inr (Or.inl he)
    · rintro (he|he|he)
      · exact Or.inl he.1
      · exact Or.inr he
      · exact Or.inl (he.elim (fun h ↦ P.toSubgraph.edgeSet_subset h) (fun h ↦ Q.toSubgraph.edgeSet_subset h))

end Erdos583ButterflyAcrossComponentsDevelopment
