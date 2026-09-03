import Submission.Work

/-! Core-edge counting at arbitrary cycle length. The hypotheses about the
carriers' core segments are explicit; this is not unrestricted absorption. -/
namespace Erdos583CarrierCoreCountingDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583Work.BridgeGlue Erdos583Work.PentagonCarriers
open Erdos583Work.CarrierGroups
open scoped Classical
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}

/-- All noncycle members share the same finite supply of edges in the core. -/
lemma core_load_bound (T : TrailFamily G k) (i : Fin k) {r : V}
    (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (F : Finset (Fin k)) (hiF : i ∉ F) :
    C.length + (∑ j ∈ F,
      ((T.walk j).toSubgraph.edgeSet ∩ (within G C.toSubgraph.verts).edgeSet).ncard)
      ≤ C.length.choose 2 := by
  classical
  let E (j : Fin k) :=
    (T.walk j).toSubgraph.edgeSet ∩ (within G C.toSubgraph.verts).edgeSet
  let U := ⋃ j : F, E j.val
  have hUcard : U.ncard=∑ j ∈ F, (E j).ncard := by
    rw [Set.ncard_iUnion_of_finite (fun _ ↦ Set.toFinite _) ?_,
      finsum_eq_sum_of_fintype]
    · exact Finset.sum_coe_sort F (fun j ↦ (E j).ncard)
    intro j l hjl
    exact (T.disjoint (fun he ↦ hjl (Subtype.ext he))).mono
      Set.inter_subset_left Set.inter_subset_left
  have hdis : Disjoint C.toSubgraph.edgeSet U := by
    apply Set.disjoint_left.mpr
    intro e heC heU
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp heU
    exact Set.disjoint_left.mp (T.disjoint (show i ≠ j.val from fun he ↦ hiF (he.symm ▸ j.property)))
      (hi.symm ▸ heC) hj.1
  have hsub : C.toSubgraph.edgeSet ∪ U ⊆ (within G C.toSubgraph.verts).edgeSet := by
    rintro e (he | he)
    · exact subgraph_edges_within C.toSubgraph _ (Set.Subset.refl _) he
    · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
      exact hj.2
  have hb := (Set.ncard_mono hsub).trans (within_edge_bound G C.toSubgraph.verts)
  rw [Set.ncard_union_eq hdis, trail_edgeSet_ncard C hC.isTrail, hUcard,
    Walk.verts_toSubgraph, cycle_support_ncard hC] at hb
  exact hb

/-- The counting inequality for full spanning core segments is unbounded in
both cycle length and number of carriers. No maximum-score assumption is used. -/
lemma full_core_load_carrier_bound (T : TrailFamily G k) (i : Fin k) {r : V}
    (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (F : Finset (Fin k)) (hiF : i ∉ F)
    (hload : ∀ j ∈ F, C.length-1 ≤
      ((T.walk j).toSubgraph.edgeSet ∩ (within G C.toSubgraph.verts).edgeSet).ncard) :
    2*F.card+3 ≤ C.length := by
  have hb := core_load_bound T i C hC hi F hiF
  have hs := Finset.sum_le_sum hload
  have hs' : F.card*(C.length-1) ≤ ∑ j ∈ F,
      ((T.walk j).toSubgraph.edgeSet ∩ (within G C.toSubgraph.verts).edgeSet).ncard := by
    simpa using hs
  have hc : 2*C.length.choose 2 ≤ C.length*(C.length-1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_le _ _
  by_contra! hn
  have hprod := Nat.mul_le_mul_right (C.length-1)
    (show C.length ≤ 2*F.card+2 by omega)
  have hlen := hC.three_le_length
  have hsub : C.length-1+1=C.length := Nat.sub_add_cancel (by omega)
  nlinarith

lemma spanning_core_segment_load (T : TrailFamily G k) (j : Fin k) {r a b : V}
    (C : G.Walk r r) (hC : C.IsCycle) (P : G.Walk a b) (hP : P.IsPath)
    (hPv : P.toSubgraph.verts=C.toSubgraph.verts)
    (hPe : P.toSubgraph.edgeSet ⊆ (T.walk j).toSubgraph.edgeSet) :
    C.length-1 ≤
      ((T.walk j).toSubgraph.edgeSet ∩ (within G C.toSubgraph.verts).edgeSet).ncard := by
  have hs : P.toSubgraph.edgeSet ⊆
      (T.walk j).toSubgraph.edgeSet ∩ (within G C.toSubgraph.verts).edgeSet :=
    Set.subset_inter hPe (subgraph_edges_within P.toSubgraph _ (by rw [hPv]))
  have hb := Set.ncard_mono hs
  rw [trail_edgeSet_ncard P hP.isTrail] at hb
  have hv := InducedBuffer.path_vertex_ncard P hP
  rw [hPv, Walk.verts_toSubgraph, cycle_support_ncard hC] at hv
  omega

lemma spanning_core_segments_carrier_bound (T : TrailFamily G k) (i : Fin k) {r : V}
    (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (F : Finset (Fin k)) (hiF : i ∉ F)
    (hseg : ∀ j ∈ F, ∃ a b, ∃ P : G.Walk a b, P.IsPath ∧
      P.toSubgraph.verts=C.toSubgraph.verts ∧
      P.toSubgraph.edgeSet ⊆ (T.walk j).toSubgraph.edgeSet) :
    2*F.card+3 ≤ C.length := by
  apply full_core_load_carrier_bound T i C hC hi F hiF
  intro j hj
  obtain ⟨a,b,P,hP,hPv,hPe⟩ := hseg j hj
  exact spanning_core_segment_load T j C hC P hP hPv hPe

/-- Under the proposed dense-carrier hypothesis, at least one carrier must
fall short of a spanning core segment. Counting alone does not repair it. -/
lemma dense_carriers_have_core_gap (T : TrailFamily G k) (i : Fin k) {r : V}
    (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hdense : C.length ≤ 2*(carrierIndices T i C.toSubgraph.verts).card+2) :
    ∃ j ∈ carrierIndices T i C.toSubgraph.verts,
      ((T.walk j).toSubgraph.edgeSet ∩ (within G C.toSubgraph.verts).edgeSet).ncard
        < C.length-1 := by
  by_contra! hn
  have hb := full_core_load_carrier_bound T i C hC hi
    (carrierIndices T i C.toSubgraph.verts)
    (by simp [carrierIndices]) hn
  omega

end Erdos583CarrierCoreCountingDevelopment
