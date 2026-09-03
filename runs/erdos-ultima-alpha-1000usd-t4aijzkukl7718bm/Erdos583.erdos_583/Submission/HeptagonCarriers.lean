import Submission.Work
import Submission.HeptagonExcursion

/-! A whole seven-cycle has at most two normal carriers in a single-defect maximum. -/
namespace Erdos583HeptagonCarriersDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583Work.PentagonCarriers Erdos583Work.BridgeGlue Erdos583Work.CarrierGroups
open Erdos583HeptagonExcursionDevelopment
open scoped Classical
set_option maxHeartbeats 1800000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}

lemma no_three_carriers (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i j l m : Fin k) (hij : i ≠ j) (hil : i ≠ l) (him : i ≠ m)
    (hjl : j ≠ l) (hjm : j ≠ m) (hlm : l ≠ m) {r : V}
    (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hjhit : ∃ x ∈ (T.walk j).support, x ∈ C.support)
    (hlhit : ∃ x ∈ (T.walk l).support, x ∈ C.support)
    (hmhit : ∃ x ∈ (T.walk m).support, x ∈ C.support) : False := by
  obtain ⟨a,b,A,P,B,hj,hP,hPv,hPl,_,_⟩ := maximum_carrier_contiguous T hs hm i j hij C hC hl hi hjhit
  obtain ⟨c,d,D,Q,E,hl',hQ,hQv,hQl,_,_⟩ := maximum_carrier_contiguous T hs hm i l hil C hC hl hi hlhit
  obtain ⟨e,f,F,R,H,hm',hR,hRv,hRl,_,_⟩ := maximum_carrier_contiguous T hs hm i m him C hC hl hi hmhit
  have hPe : P.toSubgraph.edgeSet ⊆ (T.walk j).toSubgraph.edgeSet := by
    rw [hj]; exact middle_edges_subset A P B
  have hQe : Q.toSubgraph.edgeSet ⊆ (T.walk l).toSubgraph.edgeSet := by
    rw [hl']; exact middle_edges_subset D Q E
  have hRe : R.toSubgraph.edgeSet ⊆ (T.walk m).toSubgraph.edgeSet := by
    rw [hm']; exact middle_edges_subset F R H
  have hdCP : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet := by
    rw [←hi]; exact (T.disjoint hij).mono_right hPe
  have hdCQ : Disjoint C.toSubgraph.edgeSet Q.toSubgraph.edgeSet := by
    rw [←hi]; exact (T.disjoint hil).mono_right hQe
  have hdCR : Disjoint C.toSubgraph.edgeSet R.toSubgraph.edgeSet := by
    rw [←hi]; exact (T.disjoint him).mono_right hRe
  have hdPQ : Disjoint P.toSubgraph.edgeSet Q.toSubgraph.edgeSet := (T.disjoint hjl).mono hPe hQe
  have hdPR : Disjoint P.toSubgraph.edgeSet R.toSubgraph.edgeSet := (T.disjoint hjm).mono hPe hRe
  have hdQR : Disjoint Q.toSubgraph.edgeSet R.toSubgraph.edgeSet := (T.disjoint hlm).mono hQe hRe
  have hsub : ((C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) ∪ Q.toSubgraph.edgeSet) ∪ R.toSubgraph.edgeSet ⊆
      (within G C.toSubgraph.verts).edgeSet := by
    apply Set.union_subset
    · apply Set.union_subset
      · apply Set.union_subset
        · exact subgraph_edges_within C.toSubgraph _ (Set.Subset.refl _)
        · exact subgraph_edges_within P.toSubgraph _ (by rw [hPv])
      · exact subgraph_edges_within Q.toSubgraph _ (by rw [hQv])
    · exact subgraph_edges_within R.toSubgraph _ (by rw [hRv])
  have hcard := (Set.ncard_mono hsub).trans (within_edge_bound G C.toSubgraph.verts)
  rw [Set.ncard_union_eq (Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_left.mpr ⟨hdCR,hdPR⟩,hdQR⟩),
    Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨hdCQ,hdPQ⟩),Set.ncard_union_eq hdCP,
    trail_edgeSet_ncard C hC.isTrail,trail_edgeSet_ncard P hP.isTrail,trail_edgeSet_ncard Q hQ.isTrail,
    trail_edgeSet_ncard R hR.isTrail,Walk.verts_toSubgraph,cycle_support_ncard hC,hl,hPl,hQl,hRl] at hcard
  norm_num [Nat.choose] at hcard

lemma carrier_indices_card_le_two (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i : Fin k) {r : V} (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) :
    (carrierIndices T i C.toSubgraph.verts).card ≤ 2 := by
  by_contra! hn
  obtain ⟨j,l,m,hj,hl',hm',hjl,hjm,hlm⟩ := Finset.two_lt_card_iff.mp hn
  have hit {q : Fin k} (hq : q ∈ carrierIndices T i C.toSubgraph.verts) :
      i ≠ q ∧ ∃ x ∈ (T.walk q).support, x ∈ C.support := by
    obtain ⟨hqi,x,hx,y,hxy⟩ := (Finset.mem_filter.mp hq).2
    exact ⟨hqi.symm,x,Walk.mem_support_of_adj_toSubgraph hxy,C.mem_verts_toSubgraph.mp hx⟩
  exact no_three_carriers T hs hm i j l m (hit hj).1 (hit hl').1 (hit hm').1 hjl hjm hlm
    C hC hl hi (hit hj).2 (hit hl').2 (hit hm').2

end Erdos583HeptagonCarriersDevelopment
