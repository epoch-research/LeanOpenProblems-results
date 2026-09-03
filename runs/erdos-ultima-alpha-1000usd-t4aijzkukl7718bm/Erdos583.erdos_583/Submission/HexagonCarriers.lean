import Submission.Work
import Submission.HexagonExcursion

/-! A whole six-cycle has at most one normal carrier in a single-defect maximum. -/
namespace Erdos583HexagonCarriersDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583Work.PentagonCarriers Erdos583Work.BridgeGlue
open Erdos583HexagonExcursionDevelopment
open scoped Classical
set_option maxHeartbeats 1800000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}

lemma carrier_unique (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i j l : Fin k) (hij : i ≠ j) (hil : i ≠ l) {r : V}
    (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=6)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hjhit : ∃ x ∈ (T.walk j).support, x ∈ C.support)
    (hlhit : ∃ x ∈ (T.walk l).support, x ∈ C.support) : j=l := by
  by_contra hjl
  obtain ⟨a,b,A,P,B,hj,hP,hPv,hPl,_,_⟩ := maximum_carrier_contiguous T hs hm i j hij C hC hl hi hjhit
  obtain ⟨c,d,D,Q,E,hl',hQ,hQv,hQl,_,_⟩ := maximum_carrier_contiguous T hs hm i l hil C hC hl hi hlhit
  have hPe : P.toSubgraph.edgeSet ⊆ (T.walk j).toSubgraph.edgeSet := by
    rw [hj]; exact middle_edges_subset A P B
  have hQe : Q.toSubgraph.edgeSet ⊆ (T.walk l).toSubgraph.edgeSet := by
    rw [hl']; exact middle_edges_subset D Q E
  have hdCP : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet := by
    rw [←hi]; exact (T.disjoint hij).mono_right hPe
  have hdCQ : Disjoint C.toSubgraph.edgeSet Q.toSubgraph.edgeSet := by
    rw [←hi]; exact (T.disjoint hil).mono_right hQe
  have hdPQ : Disjoint P.toSubgraph.edgeSet Q.toSubgraph.edgeSet := (T.disjoint hjl).mono hPe hQe
  have hsub : (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) ∪ Q.toSubgraph.edgeSet ⊆
      (within G C.toSubgraph.verts).edgeSet := by
    apply Set.union_subset
    · apply Set.union_subset
      · exact subgraph_edges_within C.toSubgraph _ (Set.Subset.refl _)
      · exact subgraph_edges_within P.toSubgraph _ (by rw [hPv])
    · exact subgraph_edges_within Q.toSubgraph _ (by rw [hQv])
  have hcard := (Set.ncard_mono hsub).trans (within_edge_bound G C.toSubgraph.verts)
  rw [Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨hdCQ,hdPQ⟩),Set.ncard_union_eq hdCP,
    trail_edgeSet_ncard C hC.isTrail,trail_edgeSet_ncard P hP.isTrail,trail_edgeSet_ncard Q hQ.isTrail,
    Walk.verts_toSubgraph,cycle_support_ncard hC,hl,hPl,hQl] at hcard
  norm_num [Nat.choose] at hcard

end Erdos583HexagonCarriersDevelopment
