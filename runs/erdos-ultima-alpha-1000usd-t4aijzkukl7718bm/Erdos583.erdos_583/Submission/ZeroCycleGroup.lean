import Submission.CycleIndependent

/-! An even-budget normal group in a whole-cycle failure omits four vertices. -/
namespace Erdos583ZeroCycleGroupDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion
open Erdos583Work.VertexCritical Erdos583Work.BridgeGlue
open Erdos583Work.CyclePrefixRepair
open Erdos583CycleEdgeAbsorptionDevelopment Erdos583CycleIndependentDevelopment
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

end Erdos583ZeroCycleGroupDevelopment
