import Submission.Work
import Submission.CarrierCount
import Submission.CarrierLength
import Submission.CarrierGroups
import Submission.GroupComponents

/-! Whole-cycle length bounds from optimally exposed outside components. -/
namespace Erdos583OutsideCarrierBudgetDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion Erdos583Work.MarkedCycleGroups
open Erdos583Work.VertexCritical Erdos583Work.BridgeGlue
open Erdos583CarrierCountDevelopment Erdos583CarrierLengthDevelopment Erdos583CarrierGroupsDevelopment
open Erdos583GroupComponentsDevelopment
open scoped Classical
set_option maxHeartbeats 2400000

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

noncomputable def outsideIndices (T : TrailFamily G k) (S : Set V) : Finset (Fin k) :=
  Finset.univ.filter (fun j ↦ ¬Touches S (T.walk j).toSubgraph)

lemma outside_not_touched (T : TrailFamily G k) (S : Set V) {j : Fin k}
    (hj : j ∈ outsideIndices T S) : ¬Touches S (T.walk j).toSubgraph := (Finset.mem_filter.mp hj).2

lemma cycle_touches (T : TrailFamily G k) (i : Fin k) {r : V}
    (C : G.Walk r r) (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph) :
    Touches C.toSubgraph.verts (T.walk i).toSubgraph := by
  rw [hi]
  exact ⟨r,C.start_mem_verts_toSubgraph,C.snd,C.toSubgraph_adj_snd hC.not_nil⟩

lemma outside_carrier_partition (T : TrailFamily G k) (i : Fin k) (S : Set V)
    (hi : Touches S (T.walk i).toSubgraph) :
    (outsideIndices T S).card+(carrierIndices T i S).card+1=k := by
  classical
  have hh := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
    (fun j ↦ Touches S (T.walk j).toSubgraph)
  have hc : (Finset.univ.filter (fun j ↦ Touches S (T.walk j).toSubgraph)).card=carrierCount T S := by
    simp only [carrierCount,Finset.card_filter]
  rw [hc,Finset.card_univ,Fintype.card_fin] at hh
  have hs := carrierIndices_card T i S hi
  change carrierCount T S+(outsideIndices T S).card=k at hh
  omega

lemma outside_support_avoids (T : TrailFamily G k) (S : Set V) :
    (selectedGraph T (outsideIndices T S)).support ⊆ Sᶜ := by
  rintro x ⟨y,j,hj,hxy⟩ hx
  exact outside_not_touched T S hj ⟨x,hx,y,hxy⟩

lemma outside_support_cycle_card [Fintype V] (T : TrailFamily G k) {r : V}
    (C : G.Walk r r) (hC : C.IsCycle) :
    (selectedGraph T (outsideIndices T C.toSubgraph.verts)).support.ncard+C.length ≤ Fintype.card V := by
  have hh := Set.ncard_mono (outside_support_avoids T C.toSubgraph.verts)
  have hc : C.toSubgraph.verts.ncard=C.length := by rw [Walk.verts_toSubgraph,cycle_support_ncard hC]
  have hs := C.toSubgraph.verts.ncard_add_ncard_compl
  rw [hc,Nat.card_eq_fintype_card] at hs
  omega

noncomputable def tightComponents (T : TrailFamily G k) (B : Finset (Fin k)) :
    Finset (inducedGraph T B).ConnectedComponent :=
  Finset.univ.filter (fun D ↦ 2*(componentMembers T B D).card=(selectedGraph T (componentMembers T B D)).support.ncard+1)

lemma outside_component_rounding {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (hi : ¬(T.walk i).IsPath)
    (B : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)) (hiB : i ∉ B) :
    2*B.card ≤ (selectedGraph T B).support.ncard+(tightComponents T B).card := by
  classical
  have hb (D : (inducedGraph T B).ConnectedComponent) :
      2*(componentMembers T B D).card ≤ (selectedGraph T (componentMembers T B D)).support.ncard +
        (if 2*(componentMembers T B D).card=(selectedGraph T (componentMembers T B D)).support.ncard+1 then 1 else 0) := by
    have hh := normal_group_expands hsmall hfail T hs i hi (componentMembers T B D)
      (fun hm ↦ hiB (componentMembers_subset T B D hm)) (component_support_connected T B D)
    split_ifs <;> omega
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun D hD ↦ hb D)
  rw [←Finset.mul_sum,Finset.sum_add_distrib,sum_component_members,sum_component_support,←Finset.card_filter] at hh
  exact hh

lemma tight_outside_components_card {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {r : Fin n} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hmax : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=C.toSubgraph → PreservesIncidence T U C.toSubgraph.verts →
      carrierCount U C.toSubgraph.verts ≤ carrierCount T C.toSubgraph.verts)
    (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=C.toSubgraph → PreservesIncidence T U C.toSubgraph.verts →
      carrierCount U C.toSubgraph.verts=carrierCount T C.toSubgraph.verts →
      carrierLength T C.toSubgraph.verts ≤ carrierLength U C.toSubgraph.verts) :
    (tightComponents T (outsideIndices T C.toSubgraph.verts)).card ≤
      2*(carrierIndices T i C.toSubgraph.verts).card := by
  classical
  let B := outsideIndices T C.toSubgraph.verts
  have hiB : i ∉ B := fun hh ↦ outside_not_touched T C.toSubgraph.verts hh (cycle_touches T i C hC hi)
  have hnp := CycleEar.cycle_member_not_path T i C hC hi
  have hm := CyclePrefixRepair.maximum_of_one_defect_failure hfail T hs
  have hn := NilSlot.max_score_nonpath_no_nil T hm ⟨i,hnp⟩
  let I := {D // D ∈ tightComponents T B}
  let F (D : I) := componentMembers T B D.val
  have hFC (D : I) (x : Fin n) (hx : x ∈ (selectedGraph T (F D)).support) : x ∉ C.support := by
    intro hxC
    apply outside_support_avoids T C.toSubgraph.verts
      (SimpleGraph.support_mono (CycleGroupDisjoint.selectedGraph_mono T (componentMembers_subset T B D.val)) hx)
    exact C.mem_verts_toSubgraph.mpr hxC
  have hmark (D : I) (x : Fin n) (hx : x ∈ (selectedGraph T (F D)).support) :
      MarkedPartition (selectedGraph T (F D)) (F D).card x :=
    tight_normal_group_marked hsmall hfail T hs i hnp (F D)
      (fun hh ↦ hiB (componentMembers_subset T B D.val hh)) (component_support_connected T B D.val)
      (Finset.mem_filter.mp D.property).2 x hx
  have hhit (D : I) : ∃ j ∈ carrierIndices T i C.toSubgraph.verts,
      ∃ x ∈ (T.walk j).support, x ∈ (selectedGraph T (F D)).support := by
    obtain ⟨j,hj,x,hxj,hxD⟩ := component_meets_outside T hG B ⟨i,hiB⟩ hn D.val
    have ht : Touches C.toSubgraph.verts (T.walk j).toSubgraph := by
      by_contra hh
      exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩)
    have hji : j ≠ i := by
      rintro rfl
      exact hFC D x hxD (by rwa [←Walk.mem_verts_toSubgraph,hi,Walk.mem_verts_toSubgraph] at hxj)
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hji,ht⟩,x,hxj,hxD⟩
  have hb := marked_outside_groups_card T hs i C hC hi hmax hmin F
    (fun D hh ↦ hiB (componentMembers_subset T B D.val hh)) hFC hmark
    (fun D E hDE ↦ component_support_disjoint T B (fun he ↦ hDE (Subtype.ext he))) hhit
  simpa only [I,Fintype.card_coe] using hb

lemma optimized_cycle_carrier_bound {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {r : Fin n} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hmax : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=C.toSubgraph → PreservesIncidence T U C.toSubgraph.verts →
      carrierCount U C.toSubgraph.verts ≤ carrierCount T C.toSubgraph.verts)
    (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=C.toSubgraph → PreservesIncidence T U C.toSubgraph.verts →
      carrierCount U C.toSubgraph.verts=carrierCount T C.toSubgraph.verts →
      carrierLength T C.toSubgraph.verts ≤ carrierLength U C.toSubgraph.verts) :
    C.length+2*⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ ≤ n+4*(carrierIndices T i C.toSubgraph.verts).card+2 := by
  have hiB : i ∉ outsideIndices T C.toSubgraph.verts := fun hh ↦
    outside_not_touched T C.toSubgraph.verts hh (cycle_touches T i C hC hi)
  have hround := outside_component_rounding hsmall hfail T hs i
    (CycleEar.cycle_member_not_path T i C hC hi) _ hiB
  have hcount := tight_outside_components_card hsmall hG hfail T hs i C hC hi hmax hmin
  have hsplit := outside_carrier_partition T i C.toSubgraph.verts (cycle_touches T i C hC hi)
  have hsize := outside_support_cycle_card T C hC
  simp only [Fintype.card_fin] at hsize
  omega

lemma optimized_cycle_length_bound {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {r : Fin n} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hmax : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=C.toSubgraph → PreservesIncidence T U C.toSubgraph.verts →
      carrierCount U C.toSubgraph.verts ≤ carrierCount T C.toSubgraph.verts)
    (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=C.toSubgraph → PreservesIncidence T U C.toSubgraph.verts →
      carrierCount U C.toSubgraph.verts=carrierCount T C.toSubgraph.verts →
      carrierLength T C.toSubgraph.verts ≤ carrierLength U C.toSubgraph.verts) :
    C.length ≤ 4*(carrierIndices T i C.toSubgraph.verts).card+2 ∧
      (Odd n → C.length ≤ 4*(carrierIndices T i C.toSubgraph.verts).card+1) := by
  have hh := optimized_cycle_carrier_bound hsmall hG hfail T hs i C hC hi hmax hmin
  simp only [Fintype.card_fin,ceil_half] at hh
  constructor
  · omega
  · rintro ⟨m,hm⟩
    omega

end Erdos583OutsideCarrierBudgetDevelopment
