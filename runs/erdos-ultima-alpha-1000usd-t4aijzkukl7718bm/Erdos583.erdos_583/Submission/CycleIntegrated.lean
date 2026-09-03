import Submission.TailIntegrated

/-! Integrated cycle-edge absorption and compatible cycle/tail/carrier optimization. -/
namespace Erdos583Work
/- Root-cycle edge absorption into an optimally sized normal group. -/
namespace CycleEdgeAbsorption
open SimpleGraph _root_.Erdos583Work
open _root_.Erdos583Work.QuotaTrails _root_.Erdos583Work.QuotaSurgery
open _root_.Erdos583Work.MemberExpansion _root_.Erdos583Work.MemberNormalExpansion
open _root_.Erdos583Work.RootedTailSystem _root_.Erdos583Work.TrailNormalization
open _root_.Erdos583Work.LollipopEar _root_.Erdos583Work.EdgeAbsorption
open _root_.Erdos583Work.TailEdgeAbsorption _root_.Erdos583Work.VertexCritical _root_.Erdos583Work.BridgeGlue
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

end CycleEdgeAbsorption

/- The part of a cycle in an independent set occupies at most half the cycle. -/
namespace CycleIndependent
open SimpleGraph _root_.Erdos583Work
open scoped Classical
set_option maxHeartbeats 2400000
variable {V : Type*} {G : SimpleGraph V} {a : V}

lemma cycle_independent_card [Fintype V] (C : G.Walk a a) (hC : C.IsCycle) (S : Set V)
    (hS : ∀ x ∈ S, ∀ y ∈ S, ¬C.toSubgraph.Adj x y) :
    2*(C.toSubgraph.verts ∩ S).ncard ≤ C.length := by
  classical
  have hlen := hC.three_le_length
  letI : NeZero C.length := ⟨by omega⟩
  let v (i : Fin C.length) := C.getVert i.val
  have hv : Function.Injective v := by
    intro i j he
    exact Fin.ext (hC.getVert_injOn' (by change i.val ≤ C.length-1; have := i.isLt; omega)
      (by change j.val ≤ C.length-1; have := j.isLt; omega) he)
  have hvC (x : V) : x ∈ C.toSubgraph.verts ↔ ∃ i, v i=x := by
    rw [Walk.mem_verts_toSubgraph]
    constructor
    · intro hx
      obtain ⟨j,hj,hjl⟩ := Walk.mem_support_iff_exists_getVert.mp hx
      by_cases he : j=C.length
      · refine ⟨0,?_⟩
        simpa only [he,Walk.getVert_length,v,Fin.val_zero,Walk.getVert_zero] using hj
      · exact ⟨⟨j,by omega⟩,hj⟩
    · rintro ⟨i,rfl⟩
      exact C.getVert_mem_support _
  have hn (i : Fin C.length) : C.toSubgraph.Adj (v i) (v (i+1)) := by
    have hh := C.toSubgraph_adj_getVert i.isLt
    have he : C.getVert (i.val+1)=v (i+1) := by
      change C.getVert (i.val+1)=C.getVert ((i+1).val)
      rw [Fin.val_add,Fin.val_one', Nat.mod_eq_of_lt (show 1 < C.length by omega)]
      by_cases h : i.val+1=C.length
      · rw [h,Nat.mod_self,Walk.getVert_length,Walk.getVert_zero]
      · rw [Nat.mod_eq_of_lt (by have := i.isLt; omega)]
    rwa [he] at hh
  let A := Finset.univ.filter fun i ↦ v i ∈ S
  have hAi : (A.image v : Set V)=C.toSubgraph.verts ∩ S := by
    ext x
    simp only [Finset.mem_coe,Finset.mem_image,A,Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_inter_iff,hvC]
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,rfl⟩,hi⟩
    · rintro ⟨⟨i,rfl⟩,hi⟩
      exact ⟨i,hi,rfl⟩
  have hcard : (C.toSubgraph.verts ∩ S).ncard=A.card := by
    rw [←hAi,Set.ncard_coe_finset,Finset.card_image_of_injective _ hv]
  have hsub : A.image (fun i ↦ i+1) ⊆ Finset.univ \ A := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
    intro hh
    exact hS _ (Finset.mem_filter.mp hi).2 _ (Finset.mem_filter.mp hh).2 (hn i)
  have hb := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (fun i j h ↦ add_right_cancel h),Finset.card_sdiff_of_subset (Finset.subset_univ A),Finset.card_univ,Fintype.card_fin] at hb
  rw [hcard]
  omega

lemma cycle_length_le_twice_complement [Fintype V] (C : G.Walk a a) (hC : C.IsCycle) (S : Set V)
    (hS : ∀ x ∈ S, ∀ y ∈ S, ¬C.toSubgraph.Adj x y) :
    C.length ≤ 2*Sᶜ.ncard := by
  have hb := cycle_independent_card C hC S hS
  have he := Set.ncard_inter_add_ncard_diff_eq_ncard C.toSubgraph.verts S
  have hd : (C.toSubgraph.verts \ S).ncard ≤ Sᶜ.ncard := Set.ncard_le_ncard (fun _ hx ↦ hx.2)
  have hv : C.toSubgraph.verts.ncard=C.length := by rw [Walk.verts_toSubgraph,cycle_support_ncard hC]
  rw [hv] at he
  omega


lemma cycle_independent_inter_le_complement [Fintype V] (C : G.Walk a a) (hC : C.IsCycle) (S : Set V)
    (hS : ∀ x ∈ S, ∀ y ∈ S, ¬C.toSubgraph.Adj x y) :
    (C.toSubgraph.verts ∩ S).ncard ≤ Sᶜ.ncard := by
  have hb := cycle_independent_card C hC S hS
  have he := Set.ncard_inter_add_ncard_diff_eq_ncard C.toSubgraph.verts S
  have hd : (C.toSubgraph.verts \ S).ncard ≤ Sᶜ.ncard := Set.ncard_le_ncard (fun _ hx ↦ hx.2)
  have hv : C.toSubgraph.verts.ncard=C.length := by rw [Walk.verts_toSubgraph,cycle_support_ncard hC]
  rw [hv] at he
  omega

end CycleIndependent

/- An even-budget normal group in a whole-cycle failure omits four vertices. -/
namespace ZeroCycleGroup
open SimpleGraph _root_.Erdos583Work
open _root_.Erdos583Work.QuotaTrails _root_.Erdos583Work.MemberExpansion _root_.Erdos583Work.MemberNormalExpansion
open _root_.Erdos583Work.VertexCritical _root_.Erdos583Work.BridgeGlue
open _root_.Erdos583Work.CyclePrefixRepair
open _root_.Erdos583Work.CycleEdgeAbsorption _root_.Erdos583Work.CycleIndependent
open scoped Classical
set_option maxHeartbeats 2400000

lemma small_cycle_group_complement_ge_four {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {a : Fin n} (C : G.Walk a a) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (F : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)) (hiF : i ∉ F)
    (hc : SupportConnected (selectedGraph T F)) (hsize : (selectedGraph T F).support.ncard ≤ 2*F.card) :
    4 ≤ (selectedGraph T F).supportᶜ.ncard := by
  have horder := FreeTailAbsorption.small_normal_group_proper T i F hiF hsize
  have hlen := cycle_length_le_twice_complement C hC (selectedGraph T F).support
    (fun x hx y hy ↦ small_group_cycle_independent hsmall hfail T hs i C hC hi F hiF hc horder hsize hx hy)
  have hl := HeptagonExclusion.whole_cycle_length_ge_eight hsmall hG hfail T hs
    (maximum_of_one_defect_failure hfail T hs) i C hC hi
  omega

lemma small_cycle_group_order_bound {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {a : Fin n} (C : G.Walk a a) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (F : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)) (hiF : i ∉ F)
    (hc : SupportConnected (selectedGraph T F)) (hsize : (selectedGraph T F).support.ncard ≤ 2*F.card) :
    (selectedGraph T F).support.ncard+4 ≤ n := by
  have hb := small_cycle_group_complement_ge_four hsmall hG hfail T hs i C hC hi F hiF hc hsize
  have he := Set.ncard_add_ncard_compl (selectedGraph T F).support
  rw [show Nat.card (Fin n)=n by simp] at he
  omega


section Hitting
variable {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {a : Fin n} (C : G.Walk a a) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (F : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)) (hiF : i ∉ F)
include hsmall hG hfail hs hC hi hiF

lemma hitting_group_cycle_intersection_ge_seven
    (hhit : (C.toSubgraph.verts ∩ (selectedGraph T F).support).Nonempty) :
    7 ≤ (C.toSubgraph.verts ∩ (selectedGraph T F).support).ncard := by
  have hm := maximum_of_one_defect_failure hfail T hs
  have hn := NilSlot.max_score_nonpath_no_nil T hm ⟨i,CycleEar.cycle_member_not_path T i C hC hi⟩
  obtain ⟨x,hxC,y,j,hj,hxy⟩ := hhit
  have hij : i ≠ j := fun he ↦ hiF (he.symm ▸ hj)
  have hb := CycleIntersectionSeven.failure_cycle_intersection_ge_seven hsmall hG hfail T hs hm i j hij C hC hi
    ⟨x,Walk.mem_support_of_adj_toSubgraph hxy,C.mem_verts_toSubgraph.mp hxC⟩
  have hsub : C.toSubgraph.verts ∩ (T.walk j).toSubgraph.verts ⊆
      C.toSubgraph.verts ∩ (selectedGraph T F).support := by
    intro v hv
    refine ⟨hv.1,?_⟩
    rw [selected_support_eq T F (fun j _ ↦ hn j)]
    exact ⟨j,hj,(T.walk j).mem_verts_toSubgraph.mp hv.2⟩
  exact hb.trans (Set.ncard_le_ncard hsub)

lemma small_hitting_group_bounds (hc : SupportConnected (selectedGraph T F))
    (hsize : (selectedGraph T F).support.ncard ≤ 2*F.card)
    (hhit : (C.toSubgraph.verts ∩ (selectedGraph T F).support).Nonempty) :
    14 ≤ C.length ∧ (selectedGraph T F).support.ncard+7 ≤ n := by
  have horder := FreeTailAbsorption.small_normal_group_proper T i F hiF hsize
  have hS : ∀ x ∈ (selectedGraph T F).support, ∀ y ∈ (selectedGraph T F).support, ¬C.toSubgraph.Adj x y :=
    fun x hx y hy ↦ small_group_cycle_independent hsmall hfail T hs i C hC hi F hiF hc horder hsize hx hy
  have hb := hitting_group_cycle_intersection_ge_seven hsmall hG hfail T hs i C hC hi F hiF hhit
  have hcL := cycle_independent_card C hC (selectedGraph T F).support hS
  have hcS := cycle_independent_inter_le_complement C hC (selectedGraph T F).support hS
  have he := (selectedGraph T F).support.ncard_add_ncard_compl
  rw [show Nat.card (Fin n)=n by simp] at he
  constructor <;> omega

end Hitting

lemma zero_component_bounds {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {a : Fin n} (C : G.Walk a a) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (A : (MemberComponents.normalGraph T i).ConnectedComponent)
    (hz : (selectedGraph T (MemberComponents.componentMembers T i A)).support.ncard=
      2*(MemberComponents.componentMembers T i A).card) :
    14 ≤ C.length ∧ (selectedGraph T (MemberComponents.componentMembers T i A)).support.ncard+7 ≤ n := by
  have hm := maximum_of_one_defect_failure hfail T hs
  have hn := NilSlot.max_score_nonpath_no_nil T hm ⟨i,CycleEar.cycle_member_not_path T i C hC hi⟩
  have hhit := MemberComponents.component_meets_removed T hG i hn A
  rw [hi] at hhit
  exact small_hitting_group_bounds hsmall hG hfail T hs i C hC hi _
    (MemberComponents.removed_not_mem T i A) (MemberComponents.component_support_connected T i A)
    (by omega) hhit

end ZeroCycleGroup

/- Cycle minimization compatible with the free tail and carrier optima.
The endpoint quotas, and their square energy, are not constrained. -/
namespace FreeCycleChoice
open SimpleGraph _root_.Erdos583Work
open _root_.Erdos583Work.QuotaTrails _root_.Erdos583Work.QuotaSurgery
open _root_.Erdos583Work.LollipopEar _root_.Erdos583Work.TrailNormalization
open _root_.Erdos583Work.CarrierCount _root_.Erdos583Work.CarrierLength
open _root_.Erdos583Work.MemberExpansion _root_.Erdos583Work.VertexCritical
open _root_.Erdos583Work.MemberNormalExpansion
open _root_.Erdos583Work.CyclePrefixRepair
open scoped Classical
set_option maxHeartbeats 2400000
variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

lemma exists_free_shortest_cycle (T : TrailFamily G k) (r : V) (L : RootedCycleRep T r) :
    ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U r,
      U.score=T.score ∧
      ∀ W : TrailFamily G k, ∀ N : RootedCycleRep W r,
        W.score=U.score → M.cycle.length ≤ N.cycle.length := by
  let P (n : ℕ) := ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U r,
    U.score=T.score ∧ M.cycle.length=n
  have hex : ∃ n, P n := ⟨L.cycle.length,T,L,rfl,rfl⟩
  obtain ⟨U,M,hUs,hL⟩ := Nat.find_spec hex
  refine ⟨U,M,hUs,?_⟩
  intro W N hWs
  rw [hL]
  exact Nat.find_min' hex ⟨W,N,hWs.trans hUs,rfl⟩

lemma exists_cycle_tail_carrier_optimum (T : TrailFamily G k) (r : V) (L : RootedCycleRep T r) :
    ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U r,
      U.score=T.score ∧
      (∀ W : TrailFamily G k, ∀ N : RootedCycleRep W r,
        W.score=U.score → M.cycle.length ≤ N.cycle.length) ∧
      (∀ W : TrailFamily G k, ∀ N : RootedCycleRep W r,
        W.score=U.score → N.cycle=M.cycle → M.tail.length ≤ N.tail.length) ∧
      (∀ W : TrailFamily G k, W.score=U.score →
        (W.walk M.index).toSubgraph=(U.walk M.index).toSubgraph →
        carrierCount W (U.walk M.index).toSubgraph.verts ≤ carrierCount U (U.walk M.index).toSubgraph.verts) ∧
      (∀ W : TrailFamily G k, W.score=U.score →
        (W.walk M.index).toSubgraph=(U.walk M.index).toSubgraph →
        carrierCount W (U.walk M.index).toSubgraph.verts=carrierCount U (U.walk M.index).toSubgraph.verts →
        carrierLength U (U.walk M.index).toSubgraph.verts ≤ carrierLength W (U.walk M.index).toSubgraph.verts) := by
  obtain ⟨R,N,hRs,hC⟩ := exists_free_shortest_cycle T r L
  obtain ⟨U,M,hUs,hMC,hTail,hMax,hMin⟩ := JointTailCarrier.exists_joint_optimum R r N
  refine ⟨U,M,hUs.trans hRs,?_,hTail,hMax,hMin⟩
  intro W P hWs
  rw [hMC]
  exact hC W P (hWs.trans hUs)

lemma free_cycle_minimum_structure {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (r : Fin n) (L : RootedCycleRep T r) (hdeg : 3 ≤ Nat.card (G.neighborSet r))
    (hmin : ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ M : RootedCycleRep W r,
      W.score=T.score → L.cycle.length ≤ M.cycle.length) :
    L.cycle.length=3 ∨ ∀ x ∈ L.cycle.support, 3 ≤ Nat.card (G.neighborSet x) := by
  by_cases h3 : L.cycle.length=3
  · exact Or.inl h3
  · right
    intro x hxC
    have hc3 := L.isCycle.three_le_length
    have h2 := NormalRemainder.cycle_degree_ge_two L.cycle L.isCycle hxC
    have hn := shortest_rooted_cycle_no_degree_two hsmall hG hfail T r L hs
      (maximum_of_one_defect_failure hfail T hs) (fun W M hWs _ ↦ hmin W M hWs) hdeg (by omega) hxC
    by_contra hlt
    exact hn (by omega)

lemma free_cycle_tail_normal_complement {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (r : Fin n) (L : RootedCycleRep T r) (hdeg : 3 ≤ Nat.card (G.neighborSet r))
    (hCmin : ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ M : RootedCycleRep W r,
      W.score=T.score → L.cycle.length ≤ M.cycle.length)
    (hTmin : ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ M : RootedCycleRep W r,
      W.score=T.score → M.cycle=L.cycle → L.tail.length ≤ M.tail.length) :
    (selectedGraph T (Finset.univ.erase L.index)).supportᶜ.ncard ≤ 1 := by
  exact NormalRemainderOne.normal_support_compl_card_le_one hsmall hG hfail T r L hs
    (maximum_of_one_defect_failure hfail T hs) hdeg
    (free_cycle_minimum_structure hsmall hG hfail T hs r L hdeg hCmin)
    (fun W M hWs _ hMC ↦ hTmin W M hWs hMC)


lemma normal_support_spanning_of_cycle_degree_three [Fintype V] (T : TrailFamily G k)
    (hG : G.Connected) (i : Fin k) {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hdeg : ∀ x ∈ C.support, 3 ≤ Nat.card (G.neighborSet x)) :
    (selectedGraph T (Finset.univ.erase i)).support=Set.univ := by
  classical
  letI : Nontrivial V := ⟨⟨a,C.snd,(C.adj_snd hC.not_nil).ne⟩⟩
  apply Set.eq_univ_of_forall
  intro v
  by_contra hv
  have hvG : v ∈ G.support := hG.preconnected.support_eq_univ.symm ▸ Set.mem_univ v
  have hvC : v ∈ C.support := by
    have hh := NormalRemainder.missing_mem_removed T i hvG hv
    rwa [←Walk.mem_verts_toSubgraph,hi,Walk.mem_verts_toSubgraph] at hh
  have he : G.neighborSet v=C.toSubgraph.neighborSet v := by
    ext w
    constructor
    · intro hw
      obtain ⟨j,hj⟩ := (T.cover s(v,w)).mp hw
      by_cases hji : j=i
      · subst j; rwa [hi] at hj
      · exact (hv ⟨w,j,by simp [hji],hj⟩).elim
    · exact C.toSubgraph.adj_sub
  have hb := hdeg v hvC
  rw [he,Nat.card_coe_set_eq,hC.ncard_neighborSet_toSubgraph_eq_two hvC] at hb
  omega

lemma free_minimum_whole_cycle_spanning {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (r : Fin n) (L : RootedCycleRep T r) (hdeg : 3 ≤ Nat.card (G.neighborSet r))
    (hmin : ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ M : RootedCycleRep W r,
      W.score=T.score → L.cycle.length ≤ M.cycle.length) (hn : L.tail.Nil) :
    (selectedGraph T (Finset.univ.erase L.index)).support=Set.univ := by
  have he : (T.walk L.index).toSubgraph=L.cycle.toSubgraph := by
    have hz : ∀ {a b c : Fin n} (P : G.Walk a b) (Q : G.Walk b c), Q.Nil →
        (P.append Q).toSubgraph=P.toSubgraph := by
      intro a b c P Q hQ
      cases hQ
      simp
    rw [L.subgraph]
    exact hz L.cycle L.tail hn
  have hl := HeptagonExclusion.whole_cycle_length_ge_eight hsmall hG hfail T hs
    (maximum_of_one_defect_failure hfail T hs) L.index L.cycle L.isCycle he
  have hcases := free_cycle_minimum_structure hsmall hG hfail T hs r L hdeg hmin
  exact normal_support_spanning_of_cycle_degree_three T hG L.index L.cycle L.isCycle he
    (hcases.resolve_left (by omega))


lemma free_cycle_tail_cubic_support {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (r : Fin n) (L : RootedCycleRep T r) (hdeg : Nat.card (G.neighborSet r)=3)
    (hCmin : ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ M : RootedCycleRep W r,
      W.score=T.score → L.cycle.length ≤ M.cycle.length)
    (hTmin : ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ M : RootedCycleRep W r,
      W.score=T.score → M.cycle=L.cycle → L.tail.length ≤ M.tail.length) (hn : ¬L.tail.Nil) :
    (selectedGraph T (Finset.univ.erase L.index)).support=({r}ᶜ : Set (Fin n)) := by
  have hb := free_cycle_tail_normal_complement hsmall hG hfail T hs r L (by omega) hCmin hTmin
  have hsub := Set.ncard_le_one_iff_subsingleton.mp hb
  have hr : r ∉ (selectedGraph T (Finset.univ.erase L.index)).support := by
    rintro ⟨y,j,hj,hrj⟩
    exact FreeTailGroups.cubic_open_root_others_avoid T r L hs
      (maximum_of_one_defect_failure hfail T hs) hdeg hn j (Finset.mem_erase.mp hj).1
      (Walk.mem_support_of_adj_toSubgraph hrj)
  ext v
  constructor
  · intro hv
    exact fun he ↦ hr ((Set.mem_singleton_iff.mp he) ▸ hv)
  · intro hv
    by_contra hno
    exact hv (Set.mem_singleton_iff.mpr (hsub hno hr))

lemma exists_free_cycle_component_certificate {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hcritical : GlobalCritical.MinimalEdges G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (r : Fin n) (L : RootedCycleRep T r) (hdeg : 3 ≤ Nat.card (G.neighborSet r)) :
    ∃ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∃ M : RootedCycleRep U r,
      U.score=T.score ∧
      (M.cycle.length=3 ∨ ∀ x ∈ M.cycle.support, 3 ≤ Nat.card (G.neighborSet x)) ∧
      (selectedGraph U (Finset.univ.erase M.index)).supportᶜ.ncard ≤ 1 ∧
      (M.tail.Nil → (selectedGraph U (Finset.univ.erase M.index)).support=Set.univ) ∧
      (Odd n → (selectedGraph U (Finset.univ.erase M.index)).support=Set.univ) ∧
      (Nat.card (G.neighborSet r)=3 → ¬M.tail.Nil →
        (selectedGraph U (Finset.univ.erase M.index)).support=({r}ᶜ : Set (Fin n))) ∧
      Nat.card (MemberComponents.normalGraph U M.index).ConnectedComponent ≤ 3 ∧
      (Odd n → Nat.card (MemberComponents.normalGraph U M.index).ConnectedComponent ≤ 2) ∧
      (Nat.card (G.neighborSet r)=3 → ¬M.tail.Nil →
        Nat.card (MemberComponents.normalGraph U M.index).ConnectedComponent ≤ 2) ∧
      M.cycle.length+M.tail.length ≤
        2*(CarrierGroups.carrierIndices U M.index (U.walk M.index).toSubgraph.verts).card+2 ∧
      M.cycle.length+M.tail.length+
        Nat.card (GroupComponents.inducedGraph U (OutsideCarrierBudget.outsideIndices U (U.walk M.index).toSubgraph.verts)).ConnectedComponent ≤
        2*(CarrierGroups.carrierIndices U M.index (U.walk M.index).toSubgraph.verts).card+3 := by
  obtain ⟨U,M,hUs,hCmin,hTmin,hMax,hMin⟩ := exists_cycle_tail_carrier_optimum T r L
  have hsU : U.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by omega
  have hnK : ¬IsPathSubgraph (U.walk M.index).toSubgraph := by
    rintro ⟨a,b,P,hP,hPe⟩
    exact M.member_not_path (ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (U.isTrail M.index) hP hPe)
  have hAB := AnchorCarrier.optimized_anchor_size_bound hsmall hG hfail U hsU M.index
    (U.walk M.index).toSubgraph hnK rfl hMax hMin
  have hCB := AnchorComponentBudget.anchor_component_budget hsmall hG hfail U hsU M.index
    (U.walk M.index).toSubgraph hnK rfl hMax hMin
  have hv : (U.walk M.index).toSubgraph.verts.ncard=M.cycle.length+M.tail.length := by
    rw [M.subgraph,LollipopEar.lollipop_vertex_card M.cycle M.isCycle M.tail M.isPath M.inter,Walk.length_append]
  refine ⟨U,M,hUs,free_cycle_minimum_structure hsmall hG hfail U hsU r M hdeg hCmin,
    free_cycle_tail_normal_complement hsmall hG hfail U hsU r M hdeg hCmin hTmin,
    free_minimum_whole_cycle_spanning hsmall hG hfail U hsU r M hdeg hCmin,
    (fun ho ↦ TailEar.odd_normal_support_spanning hsmall ho hG hfail U r M hsU
      (maximum_of_one_defect_failure hfail U hsU)),
    (fun hd hn ↦ free_cycle_tail_cubic_support hsmall hG hfail U hsU r M hd hCmin hTmin hn),
    FreeTailAbsorption.normal_component_count_le_three hsmall hG hfail hcritical U hsU r M hTmin,
    FreeTailAbsorption.odd_normal_component_count_le_two hsmall hG hfail hcritical U hsU r M hTmin,
    FreeTailAbsorption.cubic_open_component_count_le_two hsmall hG hfail hcritical U hsU r M hTmin,?_,?_⟩
  · have hh := hAB.1
    rwa [hv] at hh
  · have hh := hCB.1
    rwa [hv] at hh

end FreeCycleChoice

end Erdos583Work
