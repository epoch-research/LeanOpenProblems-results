import Submission.ShortTriangleDegreeFour
import Submission.DoubleSmoothTriangle

/-! External spokes of a triangle's unique ordinary carrier. -/
namespace Erdos583ShortTriangleExternalCarrierDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma unique_carrier_external_edge {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (L : RootedCycleRep T r) (j : Fin k)
    (hunique : ∀ l : Fin k, l ≠ L.index →
      (∃ v ∈ L.cycle.support, v ∈ (T.walk l).support) → l=j)
    {v z : V} (hvC : v ∈ L.cycle.support) (hvr : v ≠ r)
    (hvz : G.Adj v z) (hnC : s(v,z) ∉ L.cycle.toSubgraph.edgeSet) :
    s(v,z) ∈ (T.walk j).edges := by
  obtain ⟨l,he⟩ := (T.cover s(v,z)).mp hvz
  have hli : l ≠ L.index := by
    intro hli
    subst l
    rw [L.subgraph,Walk.toSubgraph_append,Subgraph.edgeSet_sup] at he
    have ht := he.resolve_left hnC
    exact hvr (L.inter v hvC (L.tail.fst_mem_support_of_mem_edges (L.tail.mem_edges_toSubgraph.mp ht)))
  have hlj := hunique l hli ⟨v,hvC,(T.walk l).fst_mem_support_of_mem_edges
    ((T.walk l).mem_edges_toSubgraph.mp he)⟩
  subst l
  exact (T.walk j).mem_edges_toSubgraph.mp he

lemma delete_triangle_connected_of_walk {V : Type*} {G : SimpleGraph V}
    (hG : G.Connected) {r x y u v : V} (P : G.Walk u v)
    (hr : r ∈ P.support) (hx : x ∈ P.support) (hy : y ∈ P.support)
    (havoid : ∀ e ∈ ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 V)), e ∉ P.edges) :
    SupportConnected (G.deleteEdges ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 V))) := by
  let C : Set (Sym2 V) := {s(r,x),s(x,y),s(r,y)}
  let F := G.deleteEdges C
  have ht (e : Sym2 V) (he : e ∈ P.edges) : e ∈ F.edgeSet := by
    rw [edgeSet_deleteEdges]
    exact ⟨P.edges_subset_edgeSet he,fun hc ↦ havoid e hc he⟩
  let Q := P.transfer F ht
  have hreach {z : V} (hz : z ∈ P.support) : F.Reachable u z :=
    (Q.takeUntil z (by simpa only [Q,Walk.support_transfer] using hz)).reachable
  have hedge (a b : V) (hab : G.Adj a b) : F.Reachable a b := by
    by_cases he : s(a,b) ∈ C
    · rcases he with he | he | he
      · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact (hreach hr).symm.trans (hreach hx)
        · exact (hreach hx).symm.trans (hreach hr)
      · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact (hreach hx).symm.trans (hreach hy)
        · exact (hreach hy).symm.trans (hreach hx)
      · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact (hreach hr).symm.trans (hreach hy)
        · exact (hreach hy).symm.trans (hreach hr)
    · exact (show F.Adj a b from deleteEdges_adj.mpr ⟨hab,he⟩).reachable
  intro a _ b _
  exact reachable_map_to_reachable id hedge (hG.preconnected a b)

lemma path_spoke_pairs_ne {V : Type*} [Fintype V] {G : SimpleGraph V} {u v x y a b c d : V}
    (P : G.Walk u v) (hP : P.IsPath) (hxy : x ≠ y) (hab : a ≠ b)
    (hxa : s(x,a) ∈ P.edges) (hxb : s(x,b) ∈ P.edges)
    (hyc : s(y,c) ∈ P.edges) (hyd : s(y,d) ∈ P.edges) : s(a,b) ≠ s(c,d) := by
  intro he
  have hya : s(y,a) ∈ P.edges := by
    rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hyc
    · exact hyd
  have hyb : s(y,b) ∈ P.edges := by
    rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hyd
    · exact hyc
  let F := P.toSubgraph.spanningCoe
  have fxa : F.Adj x a := P.mem_edges_toSubgraph.mpr hxa
  have fxb : F.Adj x b := P.mem_edges_toSubgraph.mpr hxb
  have fya : F.Adj y a := P.mem_edges_toSubgraph.mpr hya
  have fyb : F.Adj y b := P.mem_edges_toSubgraph.mpr hyb
  exact MatchingTrim.path_spanningCoe_isAcyclic P hP
    (QuadrilateralAbsorption.squareWalk fxa.symm fxb fyb.symm fya)
    (QuadrilateralAbsorption.square_isCycle fxa.symm fxb fyb.symm fya hab hxy)

end Erdos583ShortTriangleExternalCarrierDevelopment
