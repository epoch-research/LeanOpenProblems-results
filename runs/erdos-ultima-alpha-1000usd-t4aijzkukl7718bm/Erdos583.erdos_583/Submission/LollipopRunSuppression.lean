import Submission.CycleRunCompression
import Submission.LollipopComponentSuppression

/-! Whole-run suppression of a tail-avoiding zero-surplus normal component,
provided that at least three cycle vertices survive outside the component. -/
namespace Erdos583LollipopRunSuppressionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion
open Erdos583Work.MemberComponents Erdos583Work.BridgeGlue
open Erdos583CycleRunIntervalsDevelopment Erdos583CycleRunCompressionDevelopment
open Erdos583PathIntervalsDevelopment Erdos583LongLollipopEarDevelopment
open Erdos583NormalComponentComplementDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma subset_runs_fresh {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (root : V) (L : RootedCycleRep T root)
    (hmin : ∀ W : TrailFamily G k, ∀ M : RootedCycleRep W root,
      W.score=T.score → (∀ z, W.quota z=T.quota z) → L.cycle.length ≤ M.cycle.length)
    (A : (normalGraph T L.index).ConnectedComponent)
    (R : Set V) (hRS : R ⊆ (selectedGraph T (componentMembers T L.index A)).support)
    {t u : ℕ} (ht0 : 0 < t) (htu : t < u) (huN : u < L.cycle.length)
    (ht : L.cycle.getVert t ∉ R)
    (hu : L.cycle.getVert u ∉ R) :
    let F := selectedGraph T (Finset.univ \ componentMembers T L.index A)
    ∀ p ∈ runs L.cycle R, ¬(within F Rᶜ).Adj (runStart L.cycle p) (runFinish L.cycle p) := by
  let C := L.cycle
  let S := R
  let F := selectedGraph T (Finset.univ \ componentMembers T L.index A)
  change ∀ p ∈ runs C S, ¬(within F Rᶜ).Adj (runStart C p) (runFinish C p)
  change u < C.length at huN
  intro p hp hh
  have hr := (mem_runs C S p).mp hp
  have hab := hr.endpoint_ne C L.isCycle S ht0 (by omega) ht
  obtain ⟨j,hj,hxy⟩ := hh.1
  have hji : j ≠ L.index := by
    intro he
    subst j
    rw [L.subgraph,Walk.toSubgraph_append,Subgraph.sup_adj] at hxy
    rcases hxy with hxy|hxy
    · exact hr.shortcut_not_cycle_edge C L.isCycle S ht0 htu huN ht hu
        (C.mem_edges_toSubgraph.mp hxy)
    · have haC := C.getVert_mem_support p.val.1.val
      have hbC := C.getVert_mem_support p.val.2.val
      have haT := Walk.mem_support_of_adj_toSubgraph hxy
      have hbT := Walk.mem_support_of_adj_toSubgraph hxy.symm
      exact hab ((L.inter _ haC haT).trans (L.inter _ hbC hbT).symm)
  have hav : ∀ z ∈ (runPath C p).support, z ≠ runStart C p → z ≠ runFinish C p →
      z ∉ (T.walk j).support := by
    intro z hz hza hzb hzj
    exact Set.disjoint_left.mp (outside_member_avoids T L.index A hji (Finset.mem_sdiff.mp hj).2)
      ((T.walk j).mem_verts_toSubgraph.mpr hzj) (hRS (hr.internal_mem C S hz hza hzb))
  have hcomp := cycle_interval_complement C L.isCycle (i := p.val.1.val) (by have := p.property; omega) hr.2.1
  exact no_long_cycle_ear T root L hmin j hji.symm (runPath C p)
    ((C.drop p.val.2.val).append (C.take p.val.1.val)) hcomp.1 hcomp.2.1 hcomp.2.2
    (by rw [runPath,interval_length C _ hr.2.1]; have := p.property; omega)
    ((T.one_defect_other_paths hs L.index L.member_not_path).2 j hji)
    ((T.walk j).toSubgraph.adj_sub hxy) ((T.walk j).mem_edges_toSubgraph.mp hxy) hav

lemma tail_avoiding_runs_fresh {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (root : V) (L : RootedCycleRep T root)
    (hmin : ∀ W : TrailFamily G k, ∀ M : RootedCycleRep W root,
      W.score=T.score → (∀ z, W.quota z=T.quota z) → L.cycle.length ≤ M.cycle.length)
    (A : (normalGraph T L.index).ConnectedComponent)
    (_hTail : Disjoint L.tail.toSubgraph.verts (selectedGraph T (componentMembers T L.index A)).support)
    {t u : ℕ} (ht0 : 0 < t) (htu : t < u) (huN : u < L.cycle.length)
    (ht : L.cycle.getVert t ∉ (selectedGraph T (componentMembers T L.index A)).support)
    (hu : L.cycle.getVert u ∉ (selectedGraph T (componentMembers T L.index A)).support) :
    let S := (selectedGraph T (componentMembers T L.index A)).support
    let F := selectedGraph T (Finset.univ \ componentMembers T L.index A)
    ∀ p ∈ runs L.cycle S, ¬(within F Sᶜ).Adj (runStart L.cycle p) (runFinish L.cycle p) := by
  exact subset_runs_fresh T hs root L hmin A _ (fun _ h ↦ h) ht0 htu huN ht hu

lemma no_zero_component_away_from_tail_of_marks {n : ℕ}
    (hsmall : VertexCritical.SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (root : Fin n) (L : RootedCycleRep T root)
    (hmin : ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊,
      ∀ M : RootedCycleRep W root, W.score=T.score →
      (∀ z, W.quota z=T.quota z) → L.cycle.length ≤ M.cycle.length)
    (A : (normalGraph T L.index).ConnectedComponent)
    (hsize : (selectedGraph T (componentMembers T L.index A)).support.ncard=
      2*(componentMembers T L.index A).card)
    (hTail : Disjoint L.tail.toSubgraph.verts (selectedGraph T (componentMembers T L.index A)).support)
    {t u : ℕ} (ht0 : 0 < t) (htu : t < u) (huN : u < L.cycle.length)
    (ht : L.cycle.getVert t ∉ (selectedGraph T (componentMembers T L.index A)).support)
    (hu : L.cycle.getVert u ∉ (selectedGraph T (componentMembers T L.index A)).support) : False := by
  let B := componentMembers T L.index A
  let S := (selectedGraph T B).support
  let F := selectedGraph T (Finset.univ \ B)
  have hm := CyclePrefixRepair.maximum_of_one_defect_failure hfail T hs
  have hn := NilSlot.max_score_nonpath_no_nil T hm ⟨L.index,L.member_not_path⟩
  have hSn : S.Nonempty := by
    obtain ⟨x,_,hx⟩ := component_meets_removed T hG L.index hn A
    exact ⟨x,hx⟩
  have hSum : S.ncard+Sᶜ.ncard=n := by simpa only [Nat.card_fin] using S.ncard_add_ncard_compl
  have hSp : 0 < S.ncard := hSn.ncard_pos
  have hFc := complement_connected T hG L.index hn A
  have hroot : root ∉ S := fun hh ↦ Set.disjoint_left.mp hTail L.tail.start_mem_verts_toSubgraph hh
  have hCF : L.cycle.toSubgraph.spanningCoe ≤ F := by
    intro x y hxy
    refine ⟨L.index,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,removed_not_mem T L.index A⟩,?_⟩
    rw [L.subgraph,Walk.toSubgraph_append,Subgraph.sup_adj]
    exact Or.inl hxy
  have hF : ∀ x ∈ S, ∀ y, F.Adj x y ↔ L.cycle.toSubgraph.Adj x y := by
    intro x hx y
    rw [complement_adj_at T L.index A hx,L.subgraph,Walk.toSubgraph_append,Subgraph.sup_adj]
    constructor
    · rintro (hh|hh)
      · exact hh
      · exact (Set.disjoint_left.mp hTail (L.tail.toSubgraph.edge_vert hh) hx).elim
    · exact Or.inl
  obtain ⟨D,hD,hDc⟩ := cycle_run_partition hsmall L.cycle L.isCycle S hroot ht0 htu huN ht hu F hCF hF
    (tail_avoiding_runs_fresh T hs root L hmin A hTail ht0 htu huN ht hu) hFc (by omega)
  have hp (j) (hj : j ∉ Finset.univ \ B) : (T.walk j).IsPath := by
    have hjB : j ∈ B := by simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and,not_not] using hj
    exact (T.one_defect_other_paths hs L.index L.member_not_path).2 j
      ((mem_componentMembers T L.index j A).mp hjB).1
  obtain ⟨E,hE,hEc⟩ := replace_selected T (Finset.univ \ B) hp D hD
  have hcard : (Finset.univ \ B).card=⌈(Fintype.card (Fin n) : ℚ)/2⌉₊-B.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simp only [Finset.card_univ,Fintype.card_fin]
  have hBc : B.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ B
  apply hfail
  refine ⟨E,hE,?_⟩
  rw [hcard] at hEc
  change S.ncard=2*B.card at hsize
  simp only [ceil_half,Fintype.card_fin] at hDc hEc hBc ⊢
  omega

lemma no_zero_component_by_partial_suppression {n : ℕ}
    (hsmall : VertexCritical.SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (root : Fin n) (L : RootedCycleRep T root)
    (hmin : ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊,
      ∀ M : RootedCycleRep W root, W.score=T.score →
      (∀ z, W.quota z=T.quota z) → L.cycle.length ≤ M.cycle.length)
    (A : (normalGraph T L.index).ConnectedComponent)
    (hsize : (selectedGraph T (componentMembers T L.index A)).support.ncard=
      2*(componentMembers T L.index A).card)
    (hTail : Disjoint L.tail.toSubgraph.verts (selectedGraph T (componentMembers T L.index A)).support)
    (R : Set (Fin n)) (hRS : R ⊆ (selectedGraph T (componentMembers T L.index A)).support)
    (hRn : R.Nonempty)
    (hcost : ⌈(Rᶜ.ncard : ℚ)/2⌉₊ ≤
      ⌈((selectedGraph T (componentMembers T L.index A)).supportᶜ.ncard : ℚ)/2⌉₊)
    {t u : ℕ} (ht0 : 0 < t) (htu : t < u) (huN : u < L.cycle.length)
    (ht : L.cycle.getVert t ∉ R)
    (hu : L.cycle.getVert u ∉ R) : False := by
  let B := componentMembers T L.index A
  let S := (selectedGraph T B).support
  let F := selectedGraph T (Finset.univ \ B)
  have hm := CyclePrefixRepair.maximum_of_one_defect_failure hfail T hs
  have hn := NilSlot.max_score_nonpath_no_nil T hm ⟨L.index,L.member_not_path⟩
  have hSn : S.Nonempty := by
    obtain ⟨x,_,hx⟩ := component_meets_removed T hG L.index hn A
    exact ⟨x,hx⟩
  have hSum : S.ncard+Sᶜ.ncard=n := by simpa only [Nat.card_fin] using S.ncard_add_ncard_compl
  have hSp : 0 < S.ncard := hSn.ncard_pos
  have hFc := complement_connected T hG L.index hn A
  have hroot : root ∉ R := fun hh ↦ Set.disjoint_left.mp hTail L.tail.start_mem_verts_toSubgraph (hRS hh)
  have hCF : L.cycle.toSubgraph.spanningCoe ≤ F := by
    intro x y hxy
    refine ⟨L.index,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,removed_not_mem T L.index A⟩,?_⟩
    rw [L.subgraph,Walk.toSubgraph_append,Subgraph.sup_adj]
    exact Or.inl hxy
  have hF : ∀ x ∈ R, ∀ y, F.Adj x y ↔ L.cycle.toSubgraph.Adj x y := by
    intro x hx y
    rw [complement_adj_at T L.index A (hRS hx),L.subgraph,Walk.toSubgraph_append,Subgraph.sup_adj]
    constructor
    · rintro (hh|hh)
      · exact hh
      · exact (Set.disjoint_left.mp hTail (L.tail.toSubgraph.edge_vert hh) (hRS hx)).elim
    · exact Or.inl
  have hRsum : R.ncard+Rᶜ.ncard=n := by simpa only [Nat.card_fin] using R.ncard_add_ncard_compl
  have hRp : 0 < R.ncard := hRn.ncard_pos
  obtain ⟨D,hD,hDc'⟩ := cycle_run_partition hsmall L.cycle L.isCycle R hroot ht0 htu huN ht hu F hCF hF
    (subset_runs_fresh T hs root L hmin A R hRS ht0 htu huN ht hu) hFc (by omega)
  have hDc := hDc'.trans hcost
  change D.card ≤ ⌈(Sᶜ.ncard : ℚ)/2⌉₊ at hDc
  have hp (j) (hj : j ∉ Finset.univ \ B) : (T.walk j).IsPath := by
    have hjB : j ∈ B := by simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and,not_not] using hj
    exact (T.one_defect_other_paths hs L.index L.member_not_path).2 j
      ((mem_componentMembers T L.index j A).mp hjB).1
  obtain ⟨E,hE,hEc⟩ := replace_selected T (Finset.univ \ B) hp D hD
  have hcard : (Finset.univ \ B).card=⌈(Fintype.card (Fin n) : ℚ)/2⌉₊-B.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simp only [Finset.card_univ,Fintype.card_fin]
  have hBc : B.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ B
  apply hfail
  refine ⟨E,hE,?_⟩
  rw [hcard] at hEc
  change S.ncard=2*B.card at hsize
  simp only [ceil_half,Fintype.card_fin] at hDc hEc hBc ⊢
  omega

lemma no_zero_component_away_from_tail {n : ℕ}
    (hsmall : VertexCritical.SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (root : Fin n) (L : RootedCycleRep T root)
    (hmin : ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊,
      ∀ M : RootedCycleRep W root, W.score=T.score →
      (∀ z, W.quota z=T.quota z) → L.cycle.length ≤ M.cycle.length)
    (A : (normalGraph T L.index).ConnectedComponent)
    (hsize : (selectedGraph T (componentMembers T L.index A)).support.ncard=
      2*(componentMembers T L.index A).card)
    (hTail : Disjoint L.tail.toSubgraph.verts (selectedGraph T (componentMembers T L.index A)).support)
    (hout : 3 ≤ (L.cycle.toSubgraph.verts \
      (selectedGraph T (componentMembers T L.index A)).support).ncard) : False := by
  have hroot : root ∉ (selectedGraph T (componentMembers T L.index A)).support :=
    fun hh ↦ Set.disjoint_left.mp hTail L.tail.start_mem_verts_toSubgraph hh
  obtain ⟨t,u,ht0,htu,huN,ht,hu⟩ := two_ordered_outside_marks L.cycle _ hroot hout
  exact no_zero_component_away_from_tail_of_marks hsmall hG hfail T hs root L hmin A hsize hTail ht0 htu huN ht hu

open Erdos583UnifiedMinimalDefectDevelopment in
lemma zero_component_tail_hit_or_two_survivors (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (A : (normalGraph D.family D.rep.index).ConnectedComponent)
    (hzero : CycleComponentBudget.componentSurplus D.family D.rep.index A=0) :
    ¬Disjoint D.rep.tail.toSubgraph.verts
      (selectedGraph D.family (componentMembers D.family D.rep.index A)).support ∨
    (D.rep.cycle.toSubgraph.verts \
      (selectedGraph D.family (componentMembers D.family D.rep.index A)).support).ncard ≤ 2 := by
  by_cases hTail : Disjoint D.rep.tail.toSubgraph.verts
      (selectedGraph D.family (componentMembers D.family D.rep.index A)).support
  · apply Or.inr
    by_contra hout
    have hsize : (selectedGraph D.family (componentMembers D.family D.rep.index A)).support.ncard=
        2*(componentMembers D.family D.rep.index A).card :=
      le_antisymm (Nat.sub_eq_zero_iff_le.mp hzero) (normal_component_expansion F D A)
    exact no_zero_component_away_from_tail F.smaller F.connected F.failure D.family D.score D.root D.rep
      (fun W M hWs _ ↦ D.cycle_minimum W D.root M hWs) A hsize hTail (by omega)
  · exact Or.inl hTail

end Erdos583LollipopRunSuppressionDevelopment
