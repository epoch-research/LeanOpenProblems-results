import Submission.Work

/-! Deleting the first edge of one simple path preserves an indexed
path partition and moves only that path's first endpoint. -/
namespace Erdos583FirstEdgeFamilyDeletionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open scoped Classical
set_option maxHeartbeats 1600000
set_option Elab.async false

lemma tail_edgeSet {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : p.IsTrail) (hn : ¬p.Nil) :
    p.tail.toSubgraph.edgeSet=p.toSubgraph.edgeSet \ {s(a,p.snd)} := by
  have he : p.edges=s(a,p.snd)::p.tail.edges := by
    rw [←Walk.edges_cons (p.adj_snd hn),Walk.cons_tail_eq p hn]
  have hnot : s(a,p.snd) ∉ p.tail.edges := by
    have hh := hp.edges_nodup
    rw [he,List.nodup_cons] at hh
    exact hh.1
  ext e
  simp only [Walk.mem_edges_toSubgraph,Set.mem_diff,Set.mem_singleton_iff,he,List.mem_cons]
  constructor
  · intro hh
    exact ⟨Or.inr hh,fun h ↦ hnot (h ▸ hh)⟩
  · rintro ⟨hh,hne⟩
    exact hh.resolve_left hne

lemma delete_first_edge_family {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (a b : Fin k → V) (p : ∀ i, G.Walk (a i) (b i))
    (hp : ∀ i, (p i).IsPath)
    (hd : Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet))
    (hc : (⋃ i, (p i).toSubgraph.edgeSet)=G.edgeSet)
    (i : Fin k) (hn : ¬(p i).Nil) (v : V) (hv : (p i).snd=v) :
    ∃ q : ∀ j, (G.deleteEdges {s(a i,v)}).Walk (if j=i then v else a j) (b j),
      (∀ j, (q j).IsPath) ∧
      Pairwise (fun j l ↦ Disjoint (q j).toSubgraph.edgeSet (q l).toSubgraph.edgeSet) ∧
      (⋃ j, (q j).toSubgraph.edgeSet)=(G.deleteEdges {s(a i,v)}).edgeSet := by
  classical
  let H := G.deleteEdges {s(a i,v)}
  have htail : (p i).tail.toSubgraph.edgeSet=(p i).toSubgraph.edgeSet \ {s(a i,v)} := by
    simpa only [hv] using tail_edgeSet (p i) (hp i).isTrail hn
  have hfirst : s(a i,v) ∈ (p i).toSubgraph.edgeSet :=
    hv ▸ (p i).toSubgraph_adj_snd hn
  have hother (j : Fin k) (hji : j ≠ i) : s(a i,v) ∉ (p j).toSubgraph.edgeSet :=
    fun hh ↦ Set.disjoint_left.mp (hd hji) hh hfirst
  have htH : ∀ e ∈ (p i).tail.edges, e ∈ H.edgeSet := by
    intro e he
    have hh := (p i).tail.mem_edges_toSubgraph.mpr he
    rw [htail] at hh
    dsimp only [H]
    rw [edgeSet_deleteEdges]
    exact ⟨(p i).toSubgraph.edgeSet_subset hh.1,hh.2⟩
  have hpH (j : Fin k) (hji : j ≠ i) : ∀ e ∈ (p j).edges, e ∈ H.edgeSet := by
    intro e he
    dsimp only [H]
    rw [edgeSet_deleteEdges]
    refine ⟨(p j).edges_subset_edgeSet he,?_⟩
    intro hh
    exact hother j hji ((Set.mem_singleton_iff.mp hh) ▸ (p j).mem_edges_toSubgraph.mpr he)
  let qt := (p i).tail.transfer H htH
  have hqte : qt.toSubgraph.edgeSet=(p i).tail.toSubgraph.edgeSet := by
    ext e
    simp only [qt,Walk.mem_edges_toSubgraph,Walk.edges_transfer]
  let q (j : Fin k) : H.Walk (if j=i then v else a j) (b j) :=
    if hji : j=i then qt.copy (hv.trans (by simp [hji])) (by rw [hji])
    else ((p j).transfer H (hpH j hji)).copy (by simp [hji]) rfl
  have hq (j : Fin k) : (q j).IsPath := by
    dsimp only [q]
    split_ifs
    · simpa only [Walk.isPath_copy] using (hp i).tail.transfer htH
    · simpa only [Walk.isPath_copy] using (hp j).transfer (hpH j ‹_›)
  have hqe (j : Fin k) : (q j).toSubgraph.edgeSet=(p j).toSubgraph.edgeSet \ {s(a i,v)} := by
    by_cases hji : j=i
    · subst j
      simp only [q,dif_pos rfl,NormalTrailSystem.walk_copy_subgraph,hqte,htail]
    · have hnset : (p j).toSubgraph.edgeSet \ {s(a i,v)}=(p j).toSubgraph.edgeSet := by
        ext e
        constructor
        · exact fun h ↦ h.1
        · intro he
          exact ⟨he,fun h ↦ hother j hji ((Set.mem_singleton_iff.mp h) ▸ he)⟩
      rw [hnset]
      ext e
      simp only [q,dif_neg hji,NormalTrailSystem.walk_copy_subgraph,
        Walk.mem_edges_toSubgraph,Walk.edges_transfer]
  refine ⟨q,hq,?_,?_⟩
  · intro j l hjl
    rw [hqe,hqe]
    exact (hd hjl).mono Set.diff_subset Set.diff_subset
  · ext e
    simp only [hqe,Set.mem_iUnion,Set.mem_diff,edgeSet_deleteEdges]
    constructor
    · rintro ⟨j,hj,he⟩
      exact ⟨(p j).toSubgraph.edgeSet_subset hj,he⟩
    · rintro ⟨he,hn⟩
      rw [←hc] at he
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
      exact ⟨j,hj,hn⟩

end Erdos583FirstEdgeFamilyDeletionDevelopment
