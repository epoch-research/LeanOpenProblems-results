import Submission.TailIntegrated

/-! Root-cycle edge absorption into an optimally sized normal group. -/
namespace Erdos583CycleEdgeAbsorptionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion
open Erdos583Work.RootedTailSystem Erdos583Work.TrailNormalization
open Erdos583Work.LollipopEar Erdos583Work.EdgeAbsorption
open Erdos583Work.TailEdgeAbsorption Erdos583Work.VertexCritical Erdos583Work.BridgeGlue
open scoped Classical
set_option maxHeartbeats 2400000
variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

lemma absorb_repeated_first_edge [Fintype V] (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (i : Fin k) (hi : ¬(T.walk i).IsPath)
    (F : Finset (Fin k)) (hiF : i ∉ F)
    {r x b : V} (h : G.Adj r x) (P : G.Walk x b) (hP : P.IsPath)
    (ht : (Walk.cons h P).IsTrail) (he : (T.walk i).toSubgraph=(Walk.cons h P).toSubgraph)
    (D : Finset (selectedGraph T F ⊔ edge r x).Subgraph)
    (hD : GoodDecomposition (selectedGraph T F ⊔ edge r x) D) (hDc : D.card ≤ F.card) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ k := by
  let J := selectedGraph T F ⊔ edge r x
  have hJG : J ≤ G := sup_le (selectedGraph_le T F) ((edge_le_iff G).mpr (Or.inr h))
  have hOld : (T.walk i).toSubgraph.edgeSet={s(r,x)} ∪ P.toSubgraph.edgeSet := by
    rw [he,Walk.toSubgraph,Subgraph.edgeSet_sup,edgeSet_subgraphOfAdj]
  have hPsub : P.toSubgraph.edgeSet ⊆ (T.walk i).toSubgraph.edgeSet := by
    rw [hOld]; exact Set.subset_union_right
  have hd : Disjoint J.edgeSet P.toSubgraph.edgeSet := by
    rw [show J.edgeSet=(selectedGraph T F).edgeSet ∪ {s(r,x)} by
      rw [edgeSet_sup,edge_edgeSet_of_ne h.ne]]
    refine disjoint_sup_left.mpr ⟨(selected_disjoint T F i hiF).mono_right hPsub,?_⟩
    apply Set.disjoint_left.mpr
    intro d hd hdP
    have hde : d=s(r,x) := hd
    exact (Walk.isTrail_cons h P).mp ht |>.2 (P.mem_edges_toSubgraph.mp (hde ▸ hdP))
  have hu : J.edgeSet ∪ P.toSubgraph.edgeSet=
      (selectedGraph T F).edgeSet ∪ (T.walk i).toSubgraph.edgeSet := by
    rw [hOld,show J.edgeSet=(selectedGraph T F).edgeSet ∪ {s(r,x)} by
      rw [edgeSet_sup,edge_edgeSet_of_ne h.ne]]
    exact Set.union_assoc _ _ _
  obtain ⟨U,_,_,hUi,hrest,hpaths⟩ := replace_group_and_trail T i F hiF J hJG P hP.isTrail hd hu D hD hDc
  apply MatchingAppend.path_family_partition U
  intro j
  by_cases hji : j=i
  · subst j
    exact ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (U.isTrail i) hP hUi
  · by_cases hjF : j ∈ F
    · exact hpaths j hjF
    · exact ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (U.isTrail j)
        ((T.one_defect_other_paths hs i hi).2 j hji) (hrest j hjF hji)

lemma absorb_root_cycle_edge [Fintype V] (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (r : V) (L : RootedCycleRep T r)
    (F : Finset (Fin k)) (hiF : L.index ∉ F) {x : V} (hx : L.cycle.toSubgraph.Adj r x)
    (D : Finset (selectedGraph T F ⊔ edge r x).Subgraph)
    (hD : GoodDecomposition (selectedGraph T F ⊔ edge r x) D) (hDc : D.card ≤ F.card) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ k := by
  let h := L.cycle.toSubgraph.adj_sub hx
  obtain ⟨Q,hQ,hQe⟩ := CycleFirstVisits.cycle_edge_first L.cycle L.isCycle h
    (L.cycle.mem_edges_toSubgraph.mp hx)
  let P := Q.append L.tail
  have ht : (Walk.cons h P).IsTrail := by
    change ((Walk.cons h Q).append L.tail).IsTrail
    apply trail_append_of_disjoint hQ.isTrail L.isPath.isTrail
    rw [hQe]
    exact edge_disjoint_of_one_common_vertex L.cycle L.tail L.inter
  have he : (T.walk L.index).toSubgraph=(Walk.cons h P).toSubgraph := by
    change (T.walk L.index).toSubgraph=((Walk.cons h Q).append L.tail).toSubgraph
    rw [L.subgraph,Walk.toSubgraph_append,Walk.toSubgraph_append,hQe]
  have hP : P.IsPath := by
    apply path_append_of_support_intersection ((Walk.cons_isCycle_iff Q h).mp hQ).1 L.isPath
    intro z hz hzT
    apply L.inter z _ hzT
    rw [←Walk.mem_verts_toSubgraph,←hQe,Walk.mem_verts_toSubgraph]
    exact List.mem_cons_of_mem _ hz
  exact absorb_repeated_first_edge T hs L.index L.member_not_path F hiF h P hP ht he D hD hDc

lemma internal_edge_partition {n t : ℕ} (hsmall : SmallerOrders n) [Fintype V]
    (H : SimpleGraph V) (hc : SupportConnected H) {r x : V}
    (hr : r ∈ H.support) (hx : x ∈ H.support)
    (horder : H.support.ncard < n) (hsize : H.support.ncard ≤ 2*t) :
    ∃ D : Finset (H ⊔ edge r x).Subgraph, GoodDecomposition (H ⊔ edge r x) D ∧ D.card ≤ t := by
  have hsub : (H ⊔ edge r x).support ⊆ H.support := by
    intro z hz
    rcases attach_edge_support H hr hz with hzx|hz
    · exact hzx ▸ hx
    · exact hz
  have hb := Set.ncard_le_ncard hsub
  obtain ⟨D,hD,hDc⟩ := LowDegreeAdjacency.smaller_orders_on_support hsmall
    (H ⊔ edge r x) (attach_edge_connected H hc hr) (by omega)
  rw [ceil_half] at hDc
  exact ⟨D,hD,by omega⟩

lemma small_group_no_internal_root_edge {n : ℕ} (hsmall : SmallerOrders n) [Fintype V]
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k) (r : V) (L : RootedCycleRep T r)
    (F : Finset (Fin k)) (hiF : L.index ∉ F) (hc : SupportConnected (selectedGraph T F))
    (horder : (selectedGraph T F).support.ncard < n) (hsize : (selectedGraph T F).support.ncard ≤ 2*F.card)
    {x : V} (hx : L.cycle.toSubgraph.Adj r x) (hrF : r ∈ (selectedGraph T F).support) :
    x ∉ (selectedGraph T F).support := by
  intro hxF
  obtain ⟨D,hD,hDc⟩ := internal_edge_partition hsmall (selectedGraph T F) hc hrF hxF horder hsize
  exact hfail (absorb_root_cycle_edge T hs r L F hiF hx D hD hDc)

lemma small_group_root_boundary_unmarked {n : ℕ} (hsmall : SmallerOrders n) [Fintype V]
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k) (r : V) (L : RootedCycleRep T r)
    (F : Finset (Fin k)) (hiF : L.index ∉ F) (hc : SupportConnected (selectedGraph T F))
    (horder : (selectedGraph T F).support.ncard < n) (hsize : (selectedGraph T F).support.ncard ≤ 2*F.card)
    {x : V} (hx : L.cycle.toSubgraph.Adj r x) (hxF : x ∈ (selectedGraph T F).support) :
    ¬MarkedCycleGroups.MarkedPartition (selectedGraph T F) F.card x := by
  intro hm
  obtain ⟨D,hD,hDc⟩ := MarkedAbsorption.marked_edge_partition hsmall (selectedGraph T F) hc
    hx.ne.symm hxF horder hsize hm
  have hex : ∃ D : Finset (selectedGraph T F ⊔ edge r x).Subgraph,
      GoodDecomposition (selectedGraph T F ⊔ edge r x) D ∧ D.card ≤ F.card := by
    have hh : ∃ D : Finset (selectedGraph T F ⊔ edge x r).Subgraph,
        GoodDecomposition (selectedGraph T F ⊔ edge x r) D ∧ D.card ≤ F.card := ⟨D,hD,hDc⟩
    rw [edge_comm x r] at hh
    exact hh
  obtain ⟨D,hD,hDc⟩ := hex
  exact hfail (absorb_root_cycle_edge T hs r L F hiF hx D hD hDc)


lemma absorb_whole_cycle_edge [Fintype V] (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (i : Fin k) {a : V} (C : G.Walk a a)
    (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (F : Finset (Fin k)) (hiF : i ∉ F) {x y : V} (hxy : C.toSubgraph.Adj x y)
    (D : Finset (selectedGraph T F ⊔ edge x y).Subgraph)
    (hD : GoodDecomposition (selectedGraph T F ⊔ edge x y) D) (hDc : D.card ≤ F.card) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ k := by
  let h := C.toSubgraph.adj_sub hxy
  obtain ⟨Q,hQ,hQe⟩ := CycleFirstVisits.cycle_edge_first C hC h (C.mem_edges_toSubgraph.mp hxy)
  exact absorb_repeated_first_edge T hs i (CycleEar.cycle_member_not_path T i C hC hi)
    F hiF h Q ((Walk.cons_isCycle_iff Q h).mp hQ).1 hQ.isTrail (hi.trans hQe.symm) D hD hDc

lemma small_group_cycle_independent {n : ℕ} (hsmall : SmallerOrders n) [Fintype V]
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k) (i : Fin k)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (F : Finset (Fin k)) (hiF : i ∉ F) (hc : SupportConnected (selectedGraph T F))
    (horder : (selectedGraph T F).support.ncard < n) (hsize : (selectedGraph T F).support.ncard ≤ 2*F.card)
    {x y : V} (hx : x ∈ (selectedGraph T F).support) (hy : y ∈ (selectedGraph T F).support) :
    ¬C.toSubgraph.Adj x y := by
  intro hxy
  obtain ⟨D,hD,hDc⟩ := internal_edge_partition hsmall (selectedGraph T F) hc hx hy horder hsize
  exact hfail (absorb_whole_cycle_edge T hs i C hC hi F hiF hxy D hD hDc)

lemma small_group_cycle_vertex_unmarked {n : ℕ} (hsmall : SmallerOrders n) [Fintype V]
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k) (i : Fin k)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (F : Finset (Fin k)) (hiF : i ∉ F) (hc : SupportConnected (selectedGraph T F))
    (horder : (selectedGraph T F).support.ncard < n) (hsize : (selectedGraph T F).support.ncard ≤ 2*F.card)
    {x : V} (hx : x ∈ (selectedGraph T F).support) (hxC : x ∈ C.support) :
    ¬MarkedCycleGroups.MarkedPartition (selectedGraph T F) F.card x := by
  intro hm
  let R := C.rotate hxC
  have hR : R.IsCycle := hC.rotate hxC
  have hedge : C.toSubgraph.Adj x R.snd := by
    rw [←C.toSubgraph_rotate hxC]
    exact R.toSubgraph_adj_snd hR.not_nil
  obtain ⟨D,hD,hDc⟩ := MarkedAbsorption.marked_edge_partition hsmall (selectedGraph T F) hc
    hedge.ne hx horder hsize hm
  exact hfail (absorb_whole_cycle_edge T hs i C hC hi F hiF hedge D hD hDc)

lemma small_group_cycle_vertex_even {n : ℕ} (hsmall : SmallerOrders n) [Fintype V]
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k) (i : Fin k)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (F : Finset (Fin k)) (hiF : i ∉ F) (hc : SupportConnected (selectedGraph T F))
    (horder : (selectedGraph T F).support.ncard < n) (hsize : (selectedGraph T F).support.ncard ≤ 2*F.card)
    {x : V} (hx : x ∈ (selectedGraph T F).support) (hxC : x ∈ C.support) :
    Even (Nat.card ((selectedGraph T F).neighborSet x)) := by
  exact MarkedAbsorption.unmarked_normal_group_even hfail T hs i
    (CycleEar.cycle_member_not_path T i C hC hi) F hiF x
    (small_group_cycle_vertex_unmarked hsmall hfail T hs i C hC hi F hiF hc horder hsize hx hxC)

end Erdos583CycleEdgeAbsorptionDevelopment
