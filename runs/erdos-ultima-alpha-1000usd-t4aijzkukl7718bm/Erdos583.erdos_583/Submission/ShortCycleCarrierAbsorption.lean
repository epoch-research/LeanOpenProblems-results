import Submission.Work

/-! The many-carrier absorption assertion for cycles of length at most seven.
This uses arbitrary finite graphs and imposes no restriction on intersections
outside the cycle. It is not an unbounded cycle-absorption theorem. -/
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.CarrierGroups
namespace Erdos583ShortCycleCarrierAbsorptionDevelopment
open scoped Classical
set_option maxHeartbeats 1600000
set_option Elab.async false
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}

omit [Fintype V] in
lemma carrier_hit (T : TrailFamily G k) (i j : Fin k) {r : V}
    (C : G.Walk r r) (hj : j ∈ carrierIndices T i C.toSubgraph.verts) :
    i ≠ j ∧ ∃ x ∈ (T.walk j).support, x ∈ C.support := by
  obtain ⟨hji,x,hx,y,hxy⟩ := (Finset.mem_filter.mp hj).2
  exact ⟨hji.symm,x,Walk.mem_support_of_adj_toSubgraph hxy,C.mem_verts_toSubgraph.mp hx⟩

lemma short_cycle_carrier_bound (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i : Fin k) {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) (hl : C.length ≤ 7) :
    2*(carrierIndices T i C.toSubgraph.verts).card+3 ≤ C.length := by
  classical
  have h3 := hC.three_le_length
  by_cases h4 : C.length ≤ 4
  · have hz : (carrierIndices T i C.toSubgraph.verts).card = 0 := by
      by_contra hn
      obtain ⟨j,hj⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hn)
      obtain ⟨hij,hjhit⟩ := carrier_hit T i j C hj
      have hb := CycleIntersectionBound.single_defect_cycle_intersection_ge_five
        T hs hm i j hij C hC hi hjhit
      have hu := Set.ncard_mono (Set.inter_subset_left (s := C.toSubgraph.verts)
        (t := (T.walk j).toSubgraph.verts))
      have hCc : C.toSubgraph.verts.ncard = C.length := by
        rw [Walk.verts_toSubgraph,cycle_support_ncard hC]
      rw [hCc] at hu
      omega
    omega
  · by_cases h7 : C.length = 7
    · have hb := HeptagonCarriers.carrier_indices_card_le_two T hs hm i C hC h7 hi
      omega
    · have hc : C.length=5 ∨ C.length=6 := by omega
      have hb : (carrierIndices T i C.toSubgraph.verts).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro j hj l hl
        obtain ⟨hij,hjhit⟩ := carrier_hit T i j C hj
        obtain ⟨hil,hlhit⟩ := carrier_hit T i l C hl
        rcases hc with hc | hc
        · exact PentagonCarriers.carrier_unique T hs hm i j l hij hil C hC hc hi hjhit hlhit
        · exact HexagonCarriers.carrier_unique T hs hm i j l hij hil C hC hc hi hjhit hlhit
      omega

lemma absorb_short_cycle_dense_carriers (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (i : Fin k) {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) (hl : C.length ≤ 7)
    (hdense : C.length ≤ 2*(carrierIndices T i C.toSubgraph.verts).card+2) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k := by
  by_contra hfail
  have hm := CyclePrefixRepair.maximum_of_one_defect_failure hfail T hs
  have hb := short_cycle_carrier_bound T hs hm i C hC hi hl
  omega

lemma score_of_cycle_and_paths (T : TrailFamily G k)
    (i : Fin k) {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hp : ∀ j, j ≠ i → (T.walk j).IsPath) :
    T.score+1=G.edgeSet.ncard+k := by
  classical
  have hlen := CarrierLength.trail_length_of_same_subgraph
    (T.walk i) C (T.isTrail i) hC.isTrail hi
  have hverts : (T.walk i).toSubgraph.verts.ncard=C.length := by
    rw [hi,Walk.verts_toSubgraph,cycle_support_ncard hC]
  have hdi : T.defect i=1 := by
    have hh := T.defect_add_vertices i
    rw [hlen,hverts] at hh
    omega
  have hsum : (∑ j, T.defect j)=1 := by
    rw [Finset.sum_eq_single i, hdi]
    · intro j _ hji
      exact (T.defect_eq_zero_iff j).mpr (hp j hji)
    · simp
  have hh := T.sum_defect_add_score
  omega

/-- A cycle of length at most seven, together with arbitrary edge-disjoint
path members covering the graph, is absorbable at the existing slot count
when its length is at most twice the number of touching path members plus
two. Paths may intersect each other anywhere, including outside the cycle. -/
lemma cycle_and_paths_absorption_le_seven (T : TrailFamily G k)
    (i : Fin k) {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hp : ∀ j, j ≠ i → (T.walk j).IsPath)
    (hl : C.length ≤ 7)
    (hdense : C.length ≤ 2*(carrierIndices T i C.toSubgraph.verts).card+2) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k := by
  exact absorb_short_cycle_dense_carriers T (score_of_cycle_and_paths T i C hC hi hp)
    i C hC hi hl hdense

end Erdos583ShortCycleCarrierAbsorptionDevelopment
