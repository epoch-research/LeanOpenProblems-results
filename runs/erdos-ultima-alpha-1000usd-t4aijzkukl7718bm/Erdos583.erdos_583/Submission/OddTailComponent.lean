import Submission.LollipopRunSuppression

/-! On odd order the two-survivor case admits one retained internal vertex
at no ceiling cost. The one-survivor case has a cut vertex. -/
namespace Erdos583OddTailComponentDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion
open Erdos583Work.MemberComponents Erdos583Work.BridgeGlue
open Erdos583CycleRunIntervalsDevelopment Erdos583LollipopRunSuppressionDevelopment
open Erdos583NormalComponentComplementDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

section Critical
variable {n : ℕ} (hsmall : VertexCritical.SmallerOrders n) (ho : Odd n)
  {G : SimpleGraph (Fin n)} (hG : G.Connected)
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

include hsmall ho hG hfail hs hmin hsize hTail

lemma no_two_survivors
    (hout : (L.cycle.toSubgraph.verts \ (selectedGraph T (componentMembers T L.index A)).support).ncard=2) :
    False := by
  let S := (selectedGraph T (componentMembers T L.index A)).support
  change (L.cycle.toSubgraph.verts \ S).ncard=2 at hout
  have hm := CyclePrefixRepair.maximum_of_one_defect_failure hfail T hs
  have hn := NilSlot.max_score_nonpath_no_nil T hm ⟨L.index,L.member_not_path⟩
  have hSn : S.Nonempty := by
    obtain ⟨x,_,hx⟩ := component_meets_removed T hG L.index hn A
    exact ⟨x,hx⟩
  have hSp := hSn.ncard_pos
  change S.ncard=2*(componentMembers T L.index A).card at hsize
  have hS2 : 2 ≤ S.ncard := by omega
  have hinter := Set.ncard_inter_add_ncard_diff_eq_ncard L.cycle.toSubgraph.verts S
  have hCcard : L.cycle.toSubgraph.verts.ncard=L.cycle.length := by
    rw [Walk.verts_toSubgraph,cycle_support_ncard L.isCycle]
  have hlen := L.isCycle.three_le_length
  obtain ⟨w,hwC,hwS⟩ := (Set.ncard_pos (Set.toFinite _)).mp
    (show 0 < (L.cycle.toSubgraph.verts ∩ S).ncard by omega)
  let R := S \ {w}
  have hRn : R.Nonempty := (Set.ncard_pos (Set.toFinite _)).mp (by
    change 0 < (S \ {w}).ncard
    rw [Set.ncard_diff_singleton_of_mem hwS]
    omega)
  have hRS : R ⊆ S := Set.diff_subset
  have hform : L.cycle.toSubgraph.verts \ R=insert w (L.cycle.toSubgraph.verts \ S) := by
    ext z
    simp only [R,Set.mem_diff,Set.mem_singleton_iff,Set.mem_insert_iff]
    constructor
    · intro hh
      by_cases he : z=w
      · exact Or.inl he
      · exact Or.inr ⟨hh.1,fun hzS ↦ hh.2 ⟨hzS,he⟩⟩
    · rintro (rfl|⟨hzC,hzS⟩)
      · exact ⟨hwC,fun hh ↦ hh.2 rfl⟩
      · exact ⟨hzC,fun hh ↦ hzS hh.1⟩
  have hRout : 3 ≤ (L.cycle.toSubgraph.verts \ R).ncard := by
    rw [hform,Set.ncard_insert_of_notMem (fun hh ↦ hh.2 hwS),hout]
  have hRform : Rᶜ=insert w Sᶜ := by
    ext z
    simp only [R,Set.mem_compl_iff,Set.mem_diff,Set.mem_singleton_iff,Set.mem_insert_iff]
    tauto
  have hRcard : Rᶜ.ncard=Sᶜ.ncard+1 := by
    rw [hRform,Set.ncard_insert_of_notMem (not_not.mpr hwS)]
  have hsum : S.ncard+Sᶜ.ncard=n := by simpa only [Nat.card_fin] using S.ncard_add_ncard_compl
  have hcost : ⌈(Rᶜ.ncard : ℚ)/2⌉₊ ≤ ⌈(Sᶜ.ncard : ℚ)/2⌉₊ := by
    simp only [ceil_half,hRcard]
    obtain ⟨k,hk⟩ := ho
    omega
  have hroot : root ∉ R := fun hh ↦ Set.disjoint_left.mp hTail L.tail.start_mem_verts_toSubgraph (hRS hh)
  obtain ⟨t,u,ht0,htu,huN,ht,hu⟩ := two_ordered_outside_marks L.cycle R hroot hRout
  exact no_zero_component_by_partial_suppression hsmall hG hfail T hs root L hmin A hsize hTail
    R hRS hRn hcost ht0 htu huN ht hu

omit hmin hsize in
lemma no_single_survivor (hnil : ¬L.tail.Nil)
    (hout : L.cycle.toSubgraph.verts \ (selectedGraph T (componentMembers T L.index A)).support ⊆ {root}) :
    False := by
  let B := componentMembers T L.index A
  let S := (selectedGraph T B).support
  let J := insert root S
  have hm := CyclePrefixRepair.maximum_of_one_defect_failure hfail T hs
  have hn := NilSlot.max_score_nonpath_no_nil T hm ⟨L.index,L.member_not_path⟩
  have hSn : S.Nonempty := by
    obtain ⟨x,_,hx⟩ := component_meets_removed T hG L.index hn A
    exact ⟨x,hx⟩
  have hroot : root ∉ S := fun hh ↦ Set.disjoint_left.mp hTail L.tail.start_mem_verts_toSubgraph hh
  have hcross : ∀ x ∈ J, ∀ y ∉ J, G.Adj x y → x=root := by
    intro x hx y hy hxy
    rcases hx with hx|hx
    · exact hx
    have hyS : y ∉ S := fun hh ↦ hy (Or.inr hh)
    obtain ⟨j,hj⟩ := (T.cover s(x,y)).mp hxy
    by_cases hjB : j ∈ B
    · exact (hyS ⟨x,j,hjB,(T.walk j).toSubgraph.symm hj⟩).elim
    by_cases hji : j=L.index
    · subst j
      rw [L.subgraph,Walk.toSubgraph_append,Subgraph.edgeSet_sup] at hj
      rcases hj with hj|hj
      · have hyr : y=root := hout ⟨L.cycle.toSubgraph.edge_vert (L.cycle.toSubgraph.symm hj),hyS⟩
        exact (hy (Or.inl hyr)).elim
      · exact (Set.disjoint_left.mp hTail (L.tail.toSubgraph.edge_vert hj) hx).elim
    · exact (Set.disjoint_left.mp (outside_member_avoids T L.index A hji hjB)
        ((T.walk j).toSubgraph.edge_vert hj) hx).elim
  have hJ2 : 2 ≤ J.ncard := by
    change 2 ≤ (insert root S).ncard
    rw [Set.ncard_insert_of_notMem hroot]
    have hh := hSn.ncard_pos
    omega
  have hfr : L.finish ≠ root := by
    intro he
    have hlen : L.tail.length=0 := by
      have hh := (Walk.isPath_iff_eq_nil (L.tail.copy rfl he)).mp (by simpa only [Walk.isPath_copy] using L.isPath)
      have := congrArg Walk.length hh
      simpa only [Walk.length_copy,Walk.length_nil] using this
    exact hnil (Walk.nil_iff_length_eq.mpr hlen)
  have hfS : L.finish ∉ S := fun hh ↦ Set.disjoint_left.mp hTail L.tail.end_mem_verts_toSubgraph hh
  have hfJ : L.finish ∉ J := by rintro (hh|hh); exact hfr hh; exact hfS hh
  have hcomp : Jᶜ.Nonempty := ⟨L.finish,hfJ⟩
  exact hfail (CutVertexReduction.single_boundary_budget hsmall ho hG J root (Or.inl rfl)
    hcross hJ2 hcomp.ncard_pos)

lemma odd_zero_component_meets_tail (hnil : ¬L.tail.Nil) : False := by
  let S := (selectedGraph T (componentMembers T L.index A)).support
  by_cases hout : 3 ≤ (L.cycle.toSubgraph.verts \ S).ncard
  · exact no_zero_component_away_from_tail hsmall hG hfail T hs root L hmin A hsize hTail hout
  by_cases htwo : (L.cycle.toSubgraph.verts \ S).ncard=2
  · exact no_two_survivors hsmall ho hG hfail T hs root L hmin A hsize hTail htwo
  have hroot : root ∈ L.cycle.toSubgraph.verts \ S :=
    ⟨L.cycle.start_mem_verts_toSubgraph,fun hh ↦ Set.disjoint_left.mp hTail L.tail.start_mem_verts_toSubgraph hh⟩
  have hsub : L.cycle.toSubgraph.verts \ S ⊆ {root} := by
    have he : L.cycle.toSubgraph.verts \ S={root} := by
      apply (Set.eq_of_subset_of_ncard_le (Set.singleton_subset_iff.mpr hroot) _).symm
      simp only [Set.ncard_singleton]
      omega
    exact he ▸ Set.Subset.rfl
  exact no_single_survivor hsmall ho hG hfail T hs root L A hTail hnil hsub

end Critical
open Erdos583UnifiedMinimalDefectDevelopment in
lemma optimized_odd_zero_component_meets_tail (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (ho : Odd F.order) (A : (normalGraph D.family D.rep.index).ConnectedComponent)
    (hzero : CycleComponentBudget.componentSurplus D.family D.rep.index A=0) :
    ¬Disjoint D.rep.tail.toSubgraph.verts
      (selectedGraph D.family (componentMembers D.family D.rep.index A)).support := by
  intro hTail
  have hsize : (selectedGraph D.family (componentMembers D.family D.rep.index A)).support.ncard=
      2*(componentMembers D.family D.rep.index A).card :=
    le_antisymm (Nat.sub_eq_zero_iff_le.mp hzero) (normal_component_expansion F D A)
  exact odd_zero_component_meets_tail F.smaller ho F.connected F.failure D.family D.score D.root D.rep
    (fun W M hWs _ ↦ D.cycle_minimum W D.root M hWs) A hsize hTail (tail_not_nil F D)

end Erdos583OddTailComponentDevelopment
