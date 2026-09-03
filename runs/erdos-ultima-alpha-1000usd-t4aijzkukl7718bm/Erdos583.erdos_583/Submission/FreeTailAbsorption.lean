import Submission.TailEdgeAbsorption

/-! Free shortest tails allow nil tails; a tight normal component can then
no longer remain attached only at the final endpoint. -/
namespace Erdos583FreeTailAbsorptionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion
open Erdos583Work.MarkedCycleGroups Erdos583Work.LollipopEar
open Erdos583Work.CyclePrefixRepair Erdos583Work.VertexCritical Erdos583Work.BridgeGlue
open Erdos583TailEdgeAbsorptionDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

lemma exists_shortest_tail (T : TrailFamily G k) (r : V) (L : RootedCycleRep T r) :
    ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U r,
      U.score=T.score ∧ M.cycle=L.cycle ∧
      ∀ W : TrailFamily G k, ∀ N : RootedCycleRep W r,
        W.score=U.score → N.cycle=M.cycle → M.tail.length ≤ N.tail.length := by
  let P (m : ℕ) := ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U r,
    U.score=T.score ∧ M.cycle=L.cycle ∧ M.tail.length=m
  have hex : ∃ m, P m := ⟨L.tail.length,T,L,rfl,rfl,rfl⟩
  obtain ⟨U,M,hUs,hC,hLen⟩ := Nat.find_spec hex
  refine ⟨U,M,hUs,hC,?_⟩
  intro W N hWs hNC
  rw [hLen]
  exact Nat.find_min' hex ⟨W,N,hWs.trans hUs,hNC.trans hC,rfl⟩

lemma fully_marked_tail_hit_is_finish [Fintype V]
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : V) (L : RootedCycleRep T r)
    (hmin : ∀ U : TrailFamily G k, ∀ M : RootedCycleRep U r,
      U.score=T.score → M.cycle=L.cycle → L.tail.length ≤ M.tail.length)
    (F : Finset (Fin k)) (hiF : L.index ∉ F)
    (hmark : ∀ x ∈ (selectedGraph T F).support, MarkedPartition (selectedGraph T F) F.card x)
    (hhit : ∃ x ∈ L.tail.support, x ∈ (selectedGraph T F).support) :
    L.finish ∈ (selectedGraph T F).support := by
  classical
  obtain ⟨y,hy,R,B,hform,hB⟩ := CycleDefect.last_hit_split L.tail (selectedGraph T F).support hhit
  obtain ⟨D,d,P,hD,hcard,hP,hnP,hPD⟩ := hmark y hy
  obtain ⟨A,hAs,hrest,_,_,hparts⟩ := GroupActivation.replace_path_group_tracked T F
    (fun j hj ↦ (T.one_defect_other_paths hs L.index L.member_not_path).2 j
      (fun he ↦ hiF (he ▸ hj))) D hD hcard
  let N : RootedCycleRep A r :=
    ⟨L.index,L.finish,(hrest L.index hiF).1.trans L.start_eq,
      (hrest L.index hiF).2.1.trans L.finish_eq,L.cycle,L.tail,L.isCycle,L.isPath,L.inter,
      (hrest L.index hiF).2.2.trans L.subgraph⟩
  obtain ⟨j,hj,hAj⟩ := hparts P.toSubgraph hPD
  have hij : N.index ≠ j := fun he ↦ hiF (he.symm ▸ hj)
  let Q := P.mapLe (selectedGraph_le T F)
  have hQ : Q.IsPath := hP.mapLe _
  have hQe : Q.toSubgraph=P.toSubgraph.map (Hom.ofLE (selectedGraph_le T F)) := by
    simp only [Q,Walk.mapLe,Walk.toSubgraph_map]
  have hBQ : ∀ x ∈ B.support, x ∈ Q.support → x=y := by
    intro x hx hxQ
    apply hB x hx
    apply path_support_subset_graph_support hP hnP x
    simpa only [Q,Walk.support_mapLe_eq_support] using hxQ
  obtain ⟨U,M,hUs,hMC,hMf,hML⟩ := FreeTailGroups.shorten_tail_at_marked_path A r N (by omega)
    j hij R B hform Q hQ (hAj.trans hQe.symm) hBQ
  have hh := hmin U M (hUs.trans hAs) hMC
  have hlen : L.tail.length=R.length+B.length := by rw [hform,Walk.length_append]
  have hnil : B.Nil := Walk.nil_iff_length_eq.mpr (by omega)
  exact hnil.eq ▸ hy

lemma small_marked_group_misses_tail {n : ℕ} (hsmall : SmallerOrders n) [Fintype V]
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : V) (L : RootedCycleRep T r) (hn : ¬L.tail.Nil)
    (hmin : ∀ U : TrailFamily G k, ∀ M : RootedCycleRep U r,
      U.score=T.score → M.cycle=L.cycle → L.tail.length ≤ M.tail.length)
    (F : Finset (Fin k)) (hiF : L.index ∉ F)
    (hc : SupportConnected (selectedGraph T F))
    (horder : (selectedGraph T F).support.ncard < n)
    (hsize : (selectedGraph T F).support.ncard ≤ 2*F.card)
    (hmark : ∀ x ∈ (selectedGraph T F).support, MarkedPartition (selectedGraph T F) F.card x) :
    Disjoint L.tail.toSubgraph.verts (selectedGraph T F).support := by
  apply Set.disjoint_left.mpr
  intro x hx hxF
  have hb := fully_marked_tail_hit_is_finish T hs r L hmin F hiF hmark
    ⟨x,L.tail.mem_verts_toSubgraph.mp hx,hxF⟩
  obtain ⟨U,M,hUs,hMC,hML⟩ := shorten_at_small_marked_group hsmall T hs r L hn F hiF hc horder hsize hb (hmark _ hb)
  have hh := hmin U M hUs hMC
  omega

lemma small_marked_group_misses_lollipop {n : ℕ} (hsmall : SmallerOrders n) [Fintype V]
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : V) (L : RootedCycleRep T r) (hn : ¬L.tail.Nil)
    (hmin : ∀ U : TrailFamily G k, ∀ M : RootedCycleRep U r,
      U.score=T.score → M.cycle=L.cycle → L.tail.length ≤ M.tail.length)
    (F : Finset (Fin k)) (hiF : L.index ∉ F)
    (hc : SupportConnected (selectedGraph T F))
    (horder : (selectedGraph T F).support.ncard < n)
    (hsize : (selectedGraph T F).support.ncard ≤ 2*F.card)
    (hmark : ∀ x ∈ (selectedGraph T F).support, MarkedPartition (selectedGraph T F) F.card x) :
    Disjoint (T.walk L.index).toSubgraph.verts (selectedGraph T F).support := by
  have htail := small_marked_group_misses_tail hsmall T hs r L hn hmin F hiF hc horder hsize hmark
  have hrF : r ∉ (selectedGraph T F).support :=
    fun hh ↦ Set.disjoint_left.mp htail L.tail.start_mem_verts_toSubgraph hh
  have hnone := NilSlot.max_score_nonpath_no_nil T (maximum_of_one_defect_failure hfail T hs)
    ⟨L.index,L.member_not_path⟩
  have hav (j : Fin k) (hj : j ∈ F) : r ∉ (T.walk j).support := by
    intro hrj
    apply hrF
    rw [selected_support_eq T F (fun j _ ↦ hnone j)]
    exact ⟨j,hj,hrj⟩
  have hcycle := fully_marked_outside_group_misses_cycle hfail T hs r L F hav hmark
  rw [L.subgraph,Walk.toSubgraph_append,Subgraph.verts_sup]
  exact hcycle.union_left htail

lemma small_normal_group_proper {n : ℕ}
    {G : SimpleGraph (Fin n)} (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (F : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)) (hiF : i ∉ F)
    (hsize : (selectedGraph T F).support.ncard ≤ 2*F.card) :
    (selectedGraph T F).support.ncard < n := by
  have hFcard : F.card < ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ F,fun hh ↦ hiF (hh.symm ▸ Finset.mem_univ i)⟩)
    simpa only [Finset.card_univ,Fintype.card_fin] using hlt
  simp only [Fintype.card_fin,ceil_half] at hFcard
  omega

section Minimal
variable {n : ℕ} (hsmall : SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
  (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (r : Fin n) (L : RootedCycleRep T r)
  (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ M : RootedCycleRep U r,
    U.score=T.score → M.cycle=L.cycle → L.tail.length ≤ M.tail.length)
include hsmall hG hfail hs hmin

lemma component_unmarked (C : (MemberComponents.normalGraph T L.index).ConnectedComponent)
    (hsize : (selectedGraph T (MemberComponents.componentMembers T L.index C)).support.ncard ≤
      2*(MemberComponents.componentMembers T L.index C).card) :
    ∃ x ∈ (selectedGraph T (MemberComponents.componentMembers T L.index C)).support,
      ¬MarkedPartition (selectedGraph T (MemberComponents.componentMembers T L.index C))
        (MemberComponents.componentMembers T L.index C).card x := by
  classical
  by_contra! hmark
  let F := MemberComponents.componentMembers T L.index C
  change (selectedGraph T F).support.ncard ≤ 2*F.card at hsize
  have hiF : L.index ∉ F := MemberComponents.removed_not_mem T L.index C
  have hc := MemberComponents.component_support_connected T L.index C
  have horder := small_normal_group_proper T L.index F hiF hsize
  have hm := maximum_of_one_defect_failure hfail T hs
  have hn := NilSlot.max_score_nonpath_no_nil T hm ⟨L.index,L.member_not_path⟩
  obtain ⟨x,hxL,hxF⟩ := MemberComponents.component_meets_removed T hG L.index hn C
  by_cases hnil : L.tail.Nil
  · have he : (T.walk L.index).toSubgraph=L.cycle.toSubgraph := by
      have hz : ∀ {a b c : Fin n} (P : G.Walk a b) (Q : G.Walk b c), Q.Nil →
          (P.append Q).toSubgraph=P.toSubgraph := by
        intro a b c P Q hQ
        cases hQ
        simp
      rw [L.subgraph]
      exact hz L.cycle L.tail hnil
    have hd := marked_normal_group_disjoint_cycle hsmall hfail T hs hm L.index L.cycle L.isCycle
      he F hiF hc hmark horder (by omega)
    exact Set.disjoint_left.mp hd (he ▸ hxL) hxF
  · exact Set.disjoint_left.mp
      (small_marked_group_misses_lollipop hsmall hfail T hs r L hnil hmin F hiF hc horder hsize hmark)
      hxL hxF

lemma component_expands (C : (MemberComponents.normalGraph T L.index).ConnectedComponent) :
    2*(MemberComponents.componentMembers T L.index C).card ≤
      (selectedGraph T (MemberComponents.componentMembers T L.index C)).support.ncard := by
  let F := MemberComponents.componentMembers T L.index C
  have hiF : L.index ∉ F := MemberComponents.removed_not_mem T L.index C
  have hc := MemberComponents.component_support_connected T L.index C
  have hb := normal_group_expands hsmall hfail T hs L.index L.member_not_path F hiF hc
  by_contra hn
  change ¬2*F.card ≤ (selectedGraph T F).support.ncard at hn
  have he : 2*F.card=(selectedGraph T F).support.ncard+1 := by omega
  obtain ⟨x,hx,hxno⟩ := component_unmarked hsmall hG hfail T hs r L hmin C (by
    change (selectedGraph T F).support.ncard ≤ 2*F.card
    omega)
  exact hxno (tight_normal_group_marked hsmall hfail T hs L.index L.member_not_path F hiF hc he x hx)

lemma normal_support_bound : 2*(⌈(Fintype.card (Fin n) : ℚ)/2⌉₊-1) ≤
    (selectedGraph T (Finset.univ.erase L.index)).support.ncard := by
  classical
  rw [←MemberComponents.sum_component_support,←MemberComponents.sum_component_members T L.index,Finset.mul_sum]
  exact Finset.sum_le_sum (fun C _ ↦ component_expands hsmall hG hfail T hs r L hmin C)

lemma component_surplus_le_two : ∑ C, CycleComponentBudget.componentSurplus T L.index C ≤ 2 := by
  have hh := CycleComponentBudget.component_surplus_identity T L.index
    (component_expands hsmall hG hfail T hs r L hmin)
  have hb : (selectedGraph T (Finset.univ.erase L.index)).support.ncard ≤ n := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using Set.ncard_le_card
      (selectedGraph T (Finset.univ.erase L.index)).support
  have hk : ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊=(n+1)/2 := by rw [ceil_half,Fintype.card_fin]
  omega

lemma odd_component_surplus_le_one (ho : Odd n) :
    ∑ C, CycleComponentBudget.componentSurplus T L.index C ≤ 1 := by
  have hh := CycleComponentBudget.component_surplus_identity T L.index
    (component_expands hsmall hG hfail T hs r L hmin)
  have hb : (selectedGraph T (Finset.univ.erase L.index)).support.ncard ≤ n := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using Set.ncard_le_card
      (selectedGraph T (Finset.univ.erase L.index)).support
  have hk : ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊=(n+1)/2 := by rw [ceil_half,Fintype.card_fin]
  obtain ⟨m,hmo⟩ := ho
  omega

lemma zero_component_large (C : (MemberComponents.normalGraph T L.index).ConnectedComponent)
    (hzero : CycleComponentBudget.componentSurplus T L.index C=0) :
    n ≤ 2*(selectedGraph T (MemberComponents.componentMembers T L.index C)).support.ncard := by
  have hb := Nat.sub_eq_zero_iff_le.mp hzero
  obtain ⟨x,hx,hxno⟩ := component_unmarked hsmall hG hfail T hs r L hmin C hb
  exact MarkedAbsorption.unmarked_normal_group_large hsmall hfail T hs L.index L.member_not_path _
    (MemberComponents.removed_not_mem T L.index C) (MemberComponents.component_support_connected T L.index C)
    hb x hx hxno

lemma zero_half_component_edge_bound
    (hcritical : GlobalCritical.MinimalEdges G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (C : (MemberComponents.normalGraph T L.index).ConnectedComponent)
    (hzero : CycleComponentBudget.componentSurplus T L.index C=0)
    (hhalf : 2*(selectedGraph T (MemberComponents.componentMembers T L.index C)).support.ncard=n) :
    G.edgeSet.ncard ≤ 2*(selectedGraph T (MemberComponents.componentMembers T L.index C)).edgeSet.ncard+1 := by
  have hb := Nat.sub_eq_zero_iff_le.mp hzero
  obtain ⟨x,hx,hxno⟩ := component_unmarked hsmall hG hfail T hs r L hmin C hb
  by_contra hn
  exact hxno (half_normal_group_marked hcritical hfail T hs L.index L.member_not_path _
    (MemberComponents.removed_not_mem T L.index C) (MemberComponents.component_support_connected T L.index C)
    hhalf (by omega) hb x hx)

lemma cubic_open_surplus_le_one (hd : Nat.card (G.neighborSet r)=3) (hn : ¬L.tail.Nil) :
    ∑ C, CycleComponentBudget.componentSurplus T L.index C ≤ 1 := by
  have hh := CycleComponentBudget.component_surplus_identity T L.index
    (component_expands hsmall hG hfail T hs r L hmin)
  have hr : r ∉ (selectedGraph T (Finset.univ.erase L.index)).support := by
    rintro ⟨y,j,hj,hrj⟩
    exact FreeTailGroups.cubic_open_root_others_avoid T r L hs
      (maximum_of_one_defect_failure hfail T hs) hd hn j (Finset.mem_erase.mp hj).1
      (Walk.mem_support_of_adj_toSubgraph hrj)
  have hb := Set.ncard_le_card (insert r (selectedGraph T (Finset.univ.erase L.index)).support)
  rw [Set.ncard_insert_of_notMem hr,show Nat.card (Fin n)=n by simp] at hb
  have hk : ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊=(n+1)/2 := by rw [ceil_half,Fintype.card_fin]
  omega

end Minimal

lemma two_components_cycle_edge_bound [Fintype V] (T : TrailFamily G k) (r : V)
    (L : RootedCycleRep T r)
    {C D : (MemberComponents.normalGraph T L.index).ConnectedComponent} (hCD : C ≠ D) :
    (selectedGraph T (MemberComponents.componentMembers T L.index C)).edgeSet.ncard+
      (selectedGraph T (MemberComponents.componentMembers T L.index D)).edgeSet.ncard+L.cycle.length ≤
        G.edgeSet.ncard := by
  let J := selectedGraph T (MemberComponents.componentMembers T L.index C)
  let K := selectedGraph T (MemberComponents.componentMembers T L.index D)
  have hJK : Disjoint J.edgeSet K.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heJ heK
    induction e using Sym2.ind with
    | h x y =>
      exact Set.disjoint_left.mp (MemberComponents.component_support_disjoint T L.index hCD) ⟨y,heJ⟩ ⟨y,heK⟩
  have hsubC : L.cycle.toSubgraph.edgeSet ⊆ (T.walk L.index).toSubgraph.edgeSet := by
    rw [L.subgraph,Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    exact Set.subset_union_left
  have hJC : Disjoint J.edgeSet L.cycle.toSubgraph.edgeSet :=
    (selected_disjoint T _ L.index (MemberComponents.removed_not_mem T L.index C)).mono_right hsubC
  have hKC : Disjoint K.edgeSet L.cycle.toSubgraph.edgeSet :=
    (selected_disjoint T _ L.index (MemberComponents.removed_not_mem T L.index D)).mono_right hsubC
  have hsub : J.edgeSet ∪ K.edgeSet ∪ L.cycle.toSubgraph.edgeSet ⊆ G.edgeSet := by
    rintro e ((he|he)|he)
    · exact edgeSet_mono (selectedGraph_le T _) he
    · exact edgeSet_mono (selectedGraph_le T _) he
    · exact L.cycle.toSubgraph.edgeSet_subset he
  have hb := Set.ncard_le_ncard hsub
  rw [Set.ncard_union_eq (hJC.union_left hKC),Set.ncard_union_eq hJK,
    trail_edgeSet_ncard L.cycle L.isCycle.isTrail] at hb
  exact hb

section Critical
variable {n : ℕ} (hsmall : SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
  (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (hcritical : GlobalCritical.MinimalEdges G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (r : Fin n) (L : RootedCycleRep T r)
  (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ M : RootedCycleRep U r,
    U.score=T.score → M.cycle=L.cycle → L.tail.length ≤ M.tail.length)
include hsmall hG hfail hcritical hs hmin

lemma zero_components_equal {C D : (MemberComponents.normalGraph T L.index).ConnectedComponent}
    (hC : CycleComponentBudget.componentSurplus T L.index C=0)
    (hD : CycleComponentBudget.componentSurplus T L.index D=0) : C=D := by
  by_contra hCD
  have hsize := Set.ncard_le_card ((selectedGraph T (MemberComponents.componentMembers T L.index C)).support ∪
    (selectedGraph T (MemberComponents.componentMembers T L.index D)).support)
  rw [Set.ncard_union_eq (MemberComponents.component_support_disjoint T L.index hCD),
    show Nat.card (Fin n)=n by simp] at hsize
  have hCl := zero_component_large hsmall hG hfail T hs r L hmin C hC
  have hDl := zero_component_large hsmall hG hfail T hs r L hmin D hD
  have hCe := zero_half_component_edge_bound hsmall hG hfail T hs r L hmin hcritical C hC (by omega)
  have hDe := zero_half_component_edge_bound hsmall hG hfail T hs r L hmin hcritical D hD (by omega)
  have hE := two_components_cycle_edge_bound T r L hCD
  have hlen := L.isCycle.three_le_length
  omega

lemma zero_component_count :
    (Finset.univ.filter fun C : (MemberComponents.normalGraph T L.index).ConnectedComponent ↦
      CycleComponentBudget.componentSurplus T L.index C=0).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro C hC D hD
  exact zero_components_equal hsmall hG hfail hcritical T hs r L hmin
    (Finset.mem_filter.mp hC).2 (Finset.mem_filter.mp hD).2

lemma component_count_le_surplus_add_one :
    Nat.card (MemberComponents.normalGraph T L.index).ConnectedComponent ≤
      (∑ C, CycleComponentBudget.componentSurplus T L.index C)+1 := by
  classical
  have hz := zero_component_count hsmall hG hfail hcritical T hs r L hmin
  have hpos : (Finset.univ.filter fun C : (MemberComponents.normalGraph T L.index).ConnectedComponent ↦
      ¬CycleComponentBudget.componentSurplus T L.index C=0).card ≤
        ∑ C, CycleComponentBudget.componentSurplus T L.index C := by
    rw [Finset.card_filter]
    exact Finset.sum_le_sum (fun C _ ↦ by split_ifs <;> omega)
  have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun C : (MemberComponents.normalGraph T L.index).ConnectedComponent ↦
      CycleComponentBudget.componentSurplus T L.index C=0)
  rw [Finset.card_univ] at hcard
  rw [Nat.card_eq_fintype_card]
  omega

lemma normal_component_count_le_three : Nat.card (MemberComponents.normalGraph T L.index).ConnectedComponent ≤ 3 := by
  have hb := component_count_le_surplus_add_one hsmall hG hfail hcritical T hs r L hmin
  have hs := component_surplus_le_two hsmall hG hfail T hs r L hmin
  omega

lemma odd_normal_component_count_le_two (ho : Odd n) :
    Nat.card (MemberComponents.normalGraph T L.index).ConnectedComponent ≤ 2 := by
  have hb := component_count_le_surplus_add_one hsmall hG hfail hcritical T hs r L hmin
  have hs := odd_component_surplus_le_one hsmall hG hfail T hs r L hmin ho
  omega

lemma cubic_open_component_count_le_two (hd : Nat.card (G.neighborSet r)=3) (hn : ¬L.tail.Nil) :
    Nat.card (MemberComponents.normalGraph T L.index).ConnectedComponent ≤ 2 := by
  have hb := component_count_le_surplus_add_one hsmall hG hfail hcritical T hs r L hmin
  have hs := cubic_open_surplus_le_one hsmall hG hfail T hs r L hmin hd hn
  omega

end Critical

lemma exists_short_tail_component_certificate {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hcritical : GlobalCritical.MinimalEdges G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (r : Fin n) (L : RootedCycleRep T r) :
    ∃ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∃ M : RootedCycleRep U r,
      U.score=T.score ∧ M.cycle=L.cycle ∧
      (∀ C : (MemberComponents.normalGraph U M.index).ConnectedComponent,
        2*(MemberComponents.componentMembers U M.index C).card ≤
          (selectedGraph U (MemberComponents.componentMembers U M.index C)).support.ncard) ∧
      Nat.card (MemberComponents.normalGraph U M.index).ConnectedComponent ≤ 3 ∧
      (Odd n → Nat.card (MemberComponents.normalGraph U M.index).ConnectedComponent ≤ 2) ∧
      (Nat.card (G.neighborSet r)=3 → ¬M.tail.Nil →
        Nat.card (MemberComponents.normalGraph U M.index).ConnectedComponent ≤ 2) ∧
      ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ N : RootedCycleRep W r,
        W.score=U.score → N.cycle=M.cycle → M.tail.length ≤ N.tail.length := by
  obtain ⟨U,M,hUs,hMC,hmin⟩ := exists_shortest_tail T r L
  have hsU : U.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by omega
  exact ⟨U,M,hUs,hMC,component_expands hsmall hG hfail U hsU r M hmin,
    normal_component_count_le_three hsmall hG hfail hcritical U hsU r M hmin,
    odd_normal_component_count_le_two hsmall hG hfail hcritical U hsU r M hmin,
    cubic_open_component_count_le_two hsmall hG hfail hcritical U hsU r M hmin,hmin⟩

end Erdos583FreeTailAbsorptionDevelopment
