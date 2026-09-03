import Submission.MixedOddTriangleReduction

/-! Deleting a short triangular defect preserves connectivity through its ordinary carriers. -/
namespace Erdos583ShortTriangleDeletionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583ShortTriangleIncidenceDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma delete_triangle_connected_of_links {V : Type*} {G : SimpleGraph V}
    (hG : G.Connected) {r x y : V}
    (hx : (G.deleteEdges ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 V))).Reachable r x)
    (hy : (G.deleteEdges ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 V))).Reachable r y) :
    SupportConnected (G.deleteEdges ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 V))) := by
  let C : Set (Sym2 V) := {s(r,x),s(x,y),s(r,y)}
  let F := G.deleteEdges C
  have hedge (u v : V) (huv : G.Adj u v) : F.Reachable u v := by
    by_cases he : s(u,v) ∈ C
    · rcases he with he | he | he
      · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hx
        · exact hx.symm
      · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hx.symm.trans hy
        · exact hy.symm.trans hx
      · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hy
        · exact hy.symm
    · exact (show F.Adj u v from deleteEdges_adj.mpr ⟨huv,he⟩).reachable
  intro u _ v _
  exact reachable_map_to_reachable id hedge (hG.preconnected u v)

lemma short_triangle_external_link {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hc : L.cycle.length=3)
    (ht : L.tail.length=1 ∨ L.tail.length=2)
    {v z : V} (hvC : v ∈ L.cycle.support) (hvr : v ≠ r)
    (hvz : G.Adj v z) (hnC : s(v,z) ∉ L.cycle.toSubgraph.edgeSet) :
    (G.deleteEdges L.cycle.toSubgraph.edgeSet).Reachable r v := by
  obtain ⟨j,he⟩ := (T.cover s(v,z)).mp hvz
  have hji : j ≠ L.index := by
    intro hji
    subst j
    rw [L.subgraph,Walk.toSubgraph_append,Subgraph.edgeSet_sup] at he
    have ht' := he.resolve_left hnC
    exact hvr (L.inter v hvC (L.tail.fst_mem_support_of_mem_edges (L.tail.mem_edges_toSubgraph.mp ht')))
  have hvj : v ∈ (T.walk j).support := (T.walk j).fst_mem_support_of_mem_edges ((T.walk j).mem_edges_toSubgraph.mp he)
  have hrj := short_triangle_member_contains_root T hs hm r L hc ht j hvC hvj
  let F := G.deleteEdges L.cycle.toSubgraph.edgeSet
  have htransfer : ∀ e ∈ (T.walk j).edges, e ∈ F.edgeSet := by
    intro e he
    rw [edgeSet_deleteEdges]
    refine ⟨(T.walk j).edges_subset_edgeSet he,?_⟩
    intro heC
    have heL : e ∈ (T.walk L.index).toSubgraph.edgeSet := by
      rw [L.subgraph,Walk.toSubgraph_append,Subgraph.edgeSet_sup]
      exact Or.inl heC
    exact Set.disjoint_left.mp (T.disjoint hji.symm) heL ((T.walk j).mem_edges_toSubgraph.mpr he)
  let P := (T.walk j).transfer F htransfer
  have hrP : r ∈ P.support := by simpa only [P,Walk.support_transfer] using hrj
  have hvP : v ∈ P.support := by simpa only [P,Walk.support_transfer] using hvj
  exact (P.takeUntil r hrP).reachable.symm.trans (P.takeUntil v hvP).reachable

lemma short_triangle_delete_connected {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hG : G.Connected) (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) {x y a c : V}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hC : L.cycle=Walk.cons hrx (Walk.cons hxy (Walk.cons hry.symm Walk.nil)))
    (ht : L.tail.length=1 ∨ L.tail.length=2)
    (hxa : G.Adj x a) (hyc : G.Adj y c) (har : a ≠ r) (hay : a ≠ y) (hcr : c ≠ r) (hcx : c ≠ x) :
    SupportConnected (G.deleteEdges ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 V))) := by
  have hc : L.cycle.length=3 := by rw [hC]; rfl
  have hCe : L.cycle.toSubgraph.edgeSet=({s(r,x),s(x,y),s(r,y)} : Set (Sym2 V)) := by
    rw [hC]
    ext e
    simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,
      List.not_mem_nil,or_false,Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := y) (b := r)]
  have hx := short_triangle_external_link T hs hm r L hc ht
    (show x ∈ L.cycle.support by rw [hC]; simp) hrx.ne.symm hxa
    (by rw [hCe]; simp [hrx.ne.symm,hxy.ne,har,hay])
  have hy := short_triangle_external_link T hs hm r L hc ht
    (show y ∈ L.cycle.support by rw [hC]; simp) hry.ne.symm hyc
    (by rw [hCe]; simp [hry.ne.symm,hxy.ne.symm,hcr,hcx])
  rw [hCe] at hx hy
  exact delete_triangle_connected_of_links hG hx hy

end Erdos583ShortTriangleDeletionDevelopment
