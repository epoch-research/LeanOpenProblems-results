import Submission.MemberComponents
import Submission.MarkedCycleGroups

/-! The component surplus of a whole-cycle single defect is at most two.
At most one component can have zero surplus, after invoking the smaller-order
doubling argument and global edge minimality at its boundary. -/
namespace Erdos583CycleComponentBudgetDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.VertexCritical Erdos583Work.BridgeGlue
open Erdos583MemberExpansionDevelopment Erdos583MemberNormalExpansionDevelopment
open Erdos583CycleGroupDisjointDevelopment Erdos583MemberComponentsDevelopment
open Erdos583MarkedCycleGroupsDevelopment
open scoped Classical
set_option maxHeartbeats 1600000

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

noncomputable def componentSurplus (T : TrailFamily G k) (i : Fin k)
    (C : (normalGraph T i).ConnectedComponent) : ℕ :=
  (selectedGraph T (componentMembers T i C)).support.ncard-2*(componentMembers T i C).card

lemma component_surplus_identity [Fintype V] (T : TrailFamily G k) (i : Fin k)
    (hexpand : ∀ C : (normalGraph T i).ConnectedComponent,
      2*(componentMembers T i C).card ≤ (selectedGraph T (componentMembers T i C)).support.ncard) :
    (∑ C, componentSurplus T i C)+2*(k-1)=
      (selectedGraph T (Finset.univ.erase i)).support.ncard := by
  classical
  calc
    _ = ∑ C : (normalGraph T i).ConnectedComponent,
        (componentSurplus T i C+2*(componentMembers T i C).card) := by
      rw [Finset.sum_add_distrib,←Finset.mul_sum,sum_component_members]
    _ = ∑ C : (normalGraph T i).ConnectedComponent,
        (selectedGraph T (componentMembers T i C)).support.ncard := by
      apply Finset.sum_congr rfl
      intro C _
      exact Nat.sub_add_cancel (hexpand C)
    _ = _ := sum_component_support T i

section Smallest
variable {n : ℕ} (hsmall : SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
  (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
    D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
  (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {a : Fin n}
  (P : G.Walk a a) (hp : P.IsCycle) (hi : (T.walk i).toSubgraph=P.toSubgraph)

include hsmall hG hfail hs hm hp hi

lemma cycle_surplus_le_two : ∑ C, componentSurplus T i C ≤ 2 := by
  have hh := component_surplus_identity T i (cycle_component_expands hsmall hG hfail T hs hm i P hp hi)
  have hb : (selectedGraph T (Finset.univ.erase i)).support.ncard ≤ n := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using Set.ncard_le_card
      (selectedGraph T (Finset.univ.erase i)).support
  have heq : ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊=(n+1)/2 := by rw [ceil_half,Fintype.card_fin]
  omega

lemma odd_cycle_surplus_le_one (ho : Odd n) : ∑ C, componentSurplus T i C ≤ 1 := by
  have hh := component_surplus_identity T i (cycle_component_expands hsmall hG hfail T hs hm i P hp hi)
  have hb : (selectedGraph T (Finset.univ.erase i)).support.ncard ≤ n := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using Set.ncard_le_card
      (selectedGraph T (Finset.univ.erase i)).support
  have heq : ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊=(n+1)/2 := by rw [ceil_half,Fintype.card_fin]
  obtain ⟨m,hmo⟩ := ho
  omega

lemma cycle_component_upper (C : (normalGraph T i).ConnectedComponent) :
    (selectedGraph T (componentMembers T i C)).support.ncard ≤ 2*(componentMembers T i C).card+2 := by
  have hsum := cycle_surplus_le_two hsmall hG hfail T hs hm i P hp hi
  have hC : componentSurplus T i C ≤ ∑ D, componentSurplus T i D :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ C)
  change (selectedGraph T (componentMembers T i C)).support.ncard-2*(componentMembers T i C).card ≤ _ at hC
  omega

lemma zero_component_large (C : (normalGraph T i).ConnectedComponent)
    (hzero : componentSurplus T i C=0) :
    n ≤ 2*(selectedGraph T (componentMembers T i C)).support.ncard := by
  by_contra hn
  have hbudget : (selectedGraph T (componentMembers T i C)).support.ncard ≤
      2*(componentMembers T i C).card := Nat.sub_eq_zero_iff_le.mp hzero
  have hd := small_normal_group_disjoint_cycle hsmall hfail T hs hm i P hp hi _ (removed_not_mem T i C)
    (component_support_connected T i C) (by omega) hbudget
  obtain ⟨x,hxi,hxC⟩ := component_meets_removed T hG i
    (NilSlot.max_score_nonpath_no_nil T hm ⟨i,CycleEar.cycle_member_not_path T i P hp hi⟩) C
  exact Set.disjoint_left.mp hd (hi ▸ hxi) hxC

lemma zero_half_component_edge_bound
    (hmin : GlobalCritical.MinimalEdges G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (C : (normalGraph T i).ConnectedComponent) (hzero : componentSurplus T i C=0)
    (hhalf : 2*(selectedGraph T (componentMembers T i C)).support.ncard=n) :
    G.edgeSet.ncard ≤ 2*(selectedGraph T (componentMembers T i C)).edgeSet.ncard+1 := by
  by_contra hn
  have hbudget : (selectedGraph T (componentMembers T i C)).support.ncard ≤
      2*(componentMembers T i C).card := Nat.sub_eq_zero_iff_le.mp hzero
  have hmark := half_normal_group_marked hmin hfail T hs i
    (CycleEar.cycle_member_not_path T i P hp hi) _ (removed_not_mem T i C)
    (component_support_connected T i C) hhalf (by omega) hbudget
  have hsize : (selectedGraph T (componentMembers T i C)).support.ncard < n := by
    have := a.isLt
    omega
  have hd := marked_normal_group_disjoint_cycle hsmall hfail T hs hm i P hp hi _
    (removed_not_mem T i C) (component_support_connected T i C) hmark hsize (by omega)
  obtain ⟨x,hxi,hxC⟩ := component_meets_removed T hG i
    (NilSlot.max_score_nonpath_no_nil T hm ⟨i,CycleEar.cycle_member_not_path T i P hp hi⟩) C
  exact Set.disjoint_left.mp hd (hi ▸ hxi) hxC

end Smallest

lemma two_component_edge_bound [Fintype V] (T : TrailFamily G k) (i : Fin k) {a : V}
    (P : G.Walk a a) (hp : P.IsCycle) (hi : (T.walk i).toSubgraph=P.toSubgraph)
    {C D : (normalGraph T i).ConnectedComponent} (hCD : C ≠ D) :
    (selectedGraph T (componentMembers T i C)).edgeSet.ncard+
      (selectedGraph T (componentMembers T i D)).edgeSet.ncard+P.length ≤ G.edgeSet.ncard := by
  let J := selectedGraph T (componentMembers T i C)
  let K := selectedGraph T (componentMembers T i D)
  have hJK : Disjoint J.edgeSet K.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heJ heK
    induction e using Sym2.ind with
    | h x y =>
      exact Set.disjoint_left.mp (component_support_disjoint T i hCD) ⟨y,heJ⟩ ⟨y,heK⟩
  have hJP : Disjoint J.edgeSet P.toSubgraph.edgeSet := by
    rw [←hi]
    exact selected_disjoint T _ i (removed_not_mem T i C)
  have hKP : Disjoint K.edgeSet P.toSubgraph.edgeSet := by
    rw [←hi]
    exact selected_disjoint T _ i (removed_not_mem T i D)
  have hsub : J.edgeSet ∪ K.edgeSet ∪ P.toSubgraph.edgeSet ⊆ G.edgeSet := by
    rintro e ((he|he)|he)
    · exact edgeSet_mono (selectedGraph_le T _) he
    · exact edgeSet_mono (selectedGraph_le T _) he
    · exact P.toSubgraph.edgeSet_subset he
  have hb := Set.ncard_le_ncard hsub
  rw [Set.ncard_union_eq (hJP.union_left hKP),Set.ncard_union_eq hJK,
    trail_edgeSet_ncard P hp.isTrail] at hb
  exact hb

section Critical
variable {n : ℕ} (hsmall : SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
  (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
    D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (hmin : GlobalCritical.MinimalEdges G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
  (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {a : Fin n}
  (P : G.Walk a a) (hp : P.IsCycle) (hi : (T.walk i).toSubgraph=P.toSubgraph)

include hsmall hG hfail hmin hs hm hp hi

lemma zero_components_equal {C D : (normalGraph T i).ConnectedComponent}
    (hC : componentSurplus T i C=0) (hD : componentSurplus T i D=0) : C=D := by
  by_contra hCD
  have hsize := Set.ncard_le_card ((selectedGraph T (componentMembers T i C)).support ∪
    (selectedGraph T (componentMembers T i D)).support)
  have hnat : Nat.card (Fin n)=n := by simp
  rw [Set.ncard_union_eq (component_support_disjoint T i hCD),hnat] at hsize
  have hCl := zero_component_large hsmall hG hfail T hs hm i P hp hi C hC
  have hDl := zero_component_large hsmall hG hfail T hs hm i P hp hi D hD
  have hCb := zero_half_component_edge_bound hsmall hG hfail T hs hm i P hp hi hmin C hC (by omega)
  have hDb := zero_half_component_edge_bound hsmall hG hfail T hs hm i P hp hi hmin D hD (by omega)
  have hE := two_component_edge_bound T i P hp hi hCD
  have hlen := hp.three_le_length
  omega

lemma zero_component_count :
    (Finset.univ.filter fun C : (normalGraph T i).ConnectedComponent ↦ componentSurplus T i C=0).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro C hC D hD
  exact zero_components_equal hsmall hG hfail hmin T hs hm i P hp hi
    (Finset.mem_filter.mp hC).2 (Finset.mem_filter.mp hD).2

lemma normal_component_count_le_three : Nat.card (normalGraph T i).ConnectedComponent ≤ 3 := by
  classical
  have hz := zero_component_count hsmall hG hfail hmin T hs hm i P hp hi
  have hsum := cycle_surplus_le_two hsmall hG hfail T hs hm i P hp hi
  have hpos : (Finset.univ.filter fun C : (normalGraph T i).ConnectedComponent ↦
      ¬componentSurplus T i C=0).card ≤ ∑ C, componentSurplus T i C := by
    rw [Finset.card_filter]
    exact Finset.sum_le_sum (fun C _ ↦ by split_ifs <;> omega)
  have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun C : (normalGraph T i).ConnectedComponent ↦ componentSurplus T i C=0)
  rw [Finset.card_univ] at hcard
  rw [Nat.card_eq_fintype_card]
  omega

lemma odd_normal_component_count_le_two (ho : Odd n) : Nat.card (normalGraph T i).ConnectedComponent ≤ 2 := by
  classical
  have hz := zero_component_count hsmall hG hfail hmin T hs hm i P hp hi
  have hsum := odd_cycle_surplus_le_one hsmall hG hfail T hs hm i P hp hi ho
  have hpos : (Finset.univ.filter fun C : (normalGraph T i).ConnectedComponent ↦
      ¬componentSurplus T i C=0).card ≤ ∑ C, componentSurplus T i C := by
    rw [Finset.card_filter]
    exact Finset.sum_le_sum (fun C _ ↦ by split_ifs <;> omega)
  have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun C : (normalGraph T i).ConnectedComponent ↦ componentSurplus T i C=0)
  rw [Finset.card_univ] at hcard
  rw [Nat.card_eq_fintype_card]
  omega

end Critical
end Erdos583CycleComponentBudgetDevelopment
