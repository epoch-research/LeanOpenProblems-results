import Submission.Work
import Submission.CyclePrefixRepair

/-! Free-quota shortest tails and fully marked outside normal groups.
Only the score, root and literal cycle are fixed in this minimization. -/
namespace Erdos583FreeTailGroupsDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion
open Erdos583Work.MarkedCycleGroups Erdos583Work.LollipopEar
open Erdos583CyclePrefixRepairDevelopment
open scoped Classical
set_option maxHeartbeats 1800000

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}

omit [Fintype V] in
lemma exists_free_shortest_tail (T : TrailFamily G k) (r : V)
    (L : RootedCycleRep T r) (hn : ¬L.tail.Nil) :
    ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U r,
      U.score=T.score ∧ M.cycle=L.cycle ∧ ¬M.tail.Nil ∧
      ∀ W : TrailFamily G k, ∀ N : RootedCycleRep W r,
        W.score=U.score → N.cycle=M.cycle → ¬N.tail.Nil → M.tail.length ≤ N.tail.length := by
  classical
  let P (m : ℕ) := ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U r,
    U.score=T.score ∧ M.cycle=L.cycle ∧ ¬M.tail.Nil ∧ M.tail.length=m
  have hex : ∃ m, P m := ⟨L.tail.length,T,L,rfl,rfl,hn,rfl⟩
  obtain ⟨U,M,hUs,hC,hN,hLen⟩ := Nat.find_spec hex
  refine ⟨U,M,hUs,hC,hN,?_⟩
  intro W N hWs hNC hNn
  rw [hLen]
  exact Nat.find_min' hex ⟨W,N,hWs.trans hUs,hNC.trans hC,hNn,rfl⟩

lemma shorten_tail_at_marked_path (T : TrailFamily G k) (r : V)
    (L : RootedCycleRep T r) (hs : T.score+1=G.edgeSet.ncard+k)
    (j : Fin k) (hij : L.index ≠ j) {y d : V}
    (R : G.Walk r y) (B : G.Walk y L.finish) (hform : L.tail=R.append B)
    (P : G.Walk y d) (hP : P.IsPath) (hPe : (T.walk j).toSubgraph=P.toSubgraph)
    (hBP : ∀ x ∈ B.support, x ∈ P.support → x=y) :
    ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U r,
      U.score=T.score ∧ M.cycle=L.cycle ∧ M.finish=y ∧ M.tail.length=R.length := by
  classical
  have hRB : (R.append B).IsPath := hform ▸ L.isPath
  have hR : R.IsPath := hRB.of_append_left
  have hint : ∀ x ∈ L.cycle.support, x ∈ R.support → x=r := by
    intro x hx hxR
    apply L.inter x hx
    rw [hform,Walk.mem_support_append_iff]
    exact Or.inl hxR
  let X := L.cycle.append R
  let Q := B.reverse.append P
  have hX : X.IsTrail := trail_append_of_disjoint L.isCycle.isTrail hR.isTrail
    (edge_disjoint_of_one_common_vertex _ _ hint)
  have hQ : Q.IsPath := path_append_of_support_intersection hRB.of_append_right.reverse hP (by
    intro x hx hxP
    exact hBP x (by simpa using hx) hxP)
  have hold := trail_append_of_disjoint L.isCycle.isTrail L.isPath.isTrail
    (edge_disjoint_of_one_common_vertex _ _ L.inter)
  have hXsub : X.toSubgraph.edgeSet ⊆ (T.walk L.index).toSubgraph.edgeSet := by
    rw [L.subgraph,hform]
    simp only [X,Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    intro e he
    simp only [Set.mem_union] at he ⊢
    tauto
  have hXB : Disjoint X.toSubgraph.edgeSet B.toSubgraph.edgeSet := by
    have ht : (X.append B).IsTrail := by simpa only [X,hform,Walk.append_assoc] using hold
    exact RootedTailSystem.append_trail_disjoint ht
  have hd : Disjoint X.toSubgraph.edgeSet Q.toSubgraph.edgeSet := by
    simp only [Q,Walk.toSubgraph_append,Subgraph.edgeSet_sup,Walk.toSubgraph_reverse]
    exact disjoint_sup_right.mpr ⟨hXB,by rw [←hPe]; exact (T.disjoint hij).mono_left hXsub⟩
  have he : X.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet=
      (T.walk L.index).toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet := by
    rw [L.subgraph,hform,hPe]
    simp only [X,Q,Walk.toSubgraph_append,Subgraph.edgeSet_sup,Walk.toSubgraph_reverse]
    ext e
    simp only [Set.mem_union]
    tauto
  obtain ⟨A,hAi,_,_,hAs⟩ := GeneralPair.replace_two T L.index j hij r y L.finish d X Q hX hQ.isTrail hd he
  have hOldLen : (T.walk L.index).length=(L.cycle.append L.tail).length := by
    rw [←trail_edgeSet_ncard _ (T.isTrail L.index),L.subgraph,trail_edgeSet_ncard _ hold]
  have hOldCard : (T.walk L.index).toSubgraph.verts.ncard=(T.walk L.index).length := by
    rw [L.subgraph,lollipop_vertex_card L.cycle L.isCycle L.tail L.isPath L.inter,hOldLen]
  have hXCard : X.toSubgraph.verts.ncard=X.length := lollipop_vertex_card L.cycle L.isCycle R hR hint
  have hOldP := (T.one_defect_other_paths hs L.index L.member_not_path).2 j hij.symm
  have hsum := congrArg Set.ncard he
  rw [Set.ncard_union_eq hd,Set.ncard_union_eq (T.disjoint hij),trail_edgeSet_ncard _ hX,
    trail_edgeSet_ncard _ hQ.isTrail,trail_edgeSet_ncard _ (T.isTrail L.index),
    trail_edgeSet_ncard _ (T.isTrail j)] at hsum
  rw [hOldCard,hXCard,(walk_vertex_ncard_eq_iff _).mpr hOldP,(walk_vertex_ncard_eq_iff _).mpr hQ] at hAs
  have hscore : A.score=T.score := by omega
  obtain ⟨U,hUs,hUa,hUb,hparts,_⟩ := replace_one_general A L.index X hX hAi.symm
  let M : RootedCycleRep U r :=
    ⟨L.index,y,hUa,hUb,L.cycle,R,L.isCycle,hR,hint,(hparts L.index).trans hAi⟩
  exact ⟨U,M,hUs.trans hscore,rfl,rfl,rfl⟩

lemma free_shortest_marked_group_tail_hit_is_finish
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : V) (L : RootedCycleRep T r)
    (hmin : ∀ U : TrailFamily G k, ∀ M : RootedCycleRep U r,
      U.score=T.score → M.cycle=L.cycle → ¬M.tail.Nil → L.tail.length ≤ M.tail.length)
    (F : Finset (Fin k)) (hav : ∀ j ∈ F, r ∉ (T.walk j).support)
    (hmark : ∀ x ∈ (selectedGraph T F).support, MarkedPartition (selectedGraph T F) F.card x)
    (hhit : ∃ x ∈ L.tail.support, x ∈ (selectedGraph T F).support) :
    L.finish ∈ (selectedGraph T F).support := by
  classical
  have hia : L.index ∉ F := by
    intro hi
    apply hav L.index hi
    rw [←Walk.mem_verts_toSubgraph,L.subgraph,Walk.mem_verts_toSubgraph,Walk.mem_support_append_iff]
    exact Or.inl L.cycle.start_mem_support
  have hrF := LollipopGroups.outside_support_avoids T r F hav
  obtain ⟨y,hy,R,B,hform,hB⟩ := CycleDefect.last_hit_split L.tail (selectedGraph T F).support hhit
  have hyr : y ≠ r := by rintro rfl; exact hrF hy
  have hnR : ¬R.Nil := fun h ↦ hyr h.eq.symm
  obtain ⟨D,d,P,hD,hcard,hP,hnP,hPD⟩ := hmark y hy
  obtain ⟨A,hAs,hrest,_,_,hparts⟩ := GroupActivation.replace_path_group_tracked T F
    (fun j hj ↦ (T.one_defect_other_paths hs L.index L.member_not_path).2 j
      (fun he ↦ hia (he ▸ hj))) D hD hcard
  let N : RootedCycleRep A r :=
    ⟨L.index,L.finish,(hrest L.index hia).1.trans L.start_eq,
      (hrest L.index hia).2.1.trans L.finish_eq,L.cycle,L.tail,L.isCycle,L.isPath,L.inter,
      (hrest L.index hia).2.2.trans L.subgraph⟩
  obtain ⟨j,hj,hAj⟩ := hparts P.toSubgraph hPD
  have hij : N.index ≠ j := fun he ↦ hia (he.symm ▸ hj)
  let Q := P.mapLe (selectedGraph_le T F)
  have hQ : Q.IsPath := hP.mapLe _
  have hQe : Q.toSubgraph=P.toSubgraph.map (Hom.ofLE (selectedGraph_le T F)) := by
    simp only [Q,Walk.mapLe,Walk.toSubgraph_map]
  have hBQ : ∀ x ∈ B.support, x ∈ Q.support → x=y := by
    intro x hx hxQ
    apply hB x hx
    apply path_support_subset_graph_support hP hnP x
    simpa only [Q,Walk.support_mapLe_eq_support] using hxQ
  obtain ⟨U,M,hUs,hMC,hMf,hML⟩ := shorten_tail_at_marked_path A r N (by omega)
    j hij R B hform Q hQ (hAj.trans hQe.symm) hBQ
  have hnM : ¬M.tail.Nil := by
    intro hn
    have hz := Walk.nil_iff_length_eq.mp hn
    rw [hML] at hz
    exact hnR (Walk.nil_iff_length_eq.mpr hz)
  have hh := hmin U M (hUs.trans hAs) hMC hnM
  have hlen : L.tail.length=R.length+B.length := by rw [hform,Walk.length_append]
  have hnil : B.Nil := Walk.nil_iff_length_eq.mpr (by omega)
  exact hnil.eq ▸ hy

lemma free_shortest_fully_marked_component_contains_finish
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hG : G.Connected) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : V) (L : RootedCycleRep T r)
    (hmin : ∀ U : TrailFamily G k, ∀ M : RootedCycleRep U r,
      U.score=T.score → M.cycle=L.cycle → ¬M.tail.Nil → L.tail.length ≤ M.tail.length)
    (C : (MemberComponents.normalGraph T L.index).ConnectedComponent)
    (hav : ∀ j ∈ MemberComponents.componentMembers T L.index C, r ∉ (T.walk j).support)
    (hmark : ∀ x ∈ (selectedGraph T (MemberComponents.componentMembers T L.index C)).support,
      MarkedPartition (selectedGraph T (MemberComponents.componentMembers T L.index C))
        (MemberComponents.componentMembers T L.index C).card x) :
    L.finish ∈ (selectedGraph T (MemberComponents.componentMembers T L.index C)).support := by
  have hm := maximum_of_one_defect_failure hfail T hs
  have hnone := NilSlot.max_score_nonpath_no_nil T hm ⟨L.index,L.member_not_path⟩
  obtain ⟨x,hxi,hxC⟩ := MemberComponents.component_meets_removed T hG L.index hnone C
  have hd := fully_marked_outside_group_misses_cycle hfail T hs r L _ hav hmark
  have hxT : x ∈ L.tail.support := by
    rw [L.subgraph,Walk.mem_verts_toSubgraph,Walk.mem_support_append_iff] at hxi
    exact hxi.resolve_left (fun hx ↦ Set.disjoint_left.mp hd (L.cycle.mem_verts_toSubgraph.mpr hx) hxC)
  exact free_shortest_marked_group_tail_hit_is_finish T hs r L hmin _ hav hmark ⟨x,hxT,hxC⟩

lemma open_rooted_member_degree (T : TrailFamily G k) (r : V)
    (L : RootedCycleRep T r) (hn : ¬L.tail.Nil) :
    ((T.walk L.index).toSubgraph.neighborSet r).ncard=3 := by
  classical
  have hd := edge_disjoint_of_one_common_vertex L.cycle L.tail L.inter
  have hN : Disjoint (L.cycle.toSubgraph.neighborSet r) (L.tail.toSubgraph.neighborSet r) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp hd (show s(r,x) ∈ L.cycle.toSubgraph.edgeSet from hx)
      (show s(r,x) ∈ L.tail.toSubgraph.edgeSet from hy)
  rw [L.subgraph,Walk.toSubgraph_append,Subgraph.neighborSet_sup,Set.ncard_union_eq hN,
    L.isCycle.ncard_neighborSet_toSubgraph_eq_two L.cycle.start_mem_support]
  have hp := path_neighbor_ncard_formula L.isPath hn r
  simpa only [eq_self_iff_true,true_or,if_true] using congrArg (2+·) hp

lemma cubic_open_root_others_avoid (T : TrailFamily G k) (r : V)
    (L : RootedCycleRep T r) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hd : Nat.card (G.neighborSet r)=3) (hn : ¬L.tail.Nil)
    (j : Fin k) (hji : j ≠ L.index) : r ∉ (T.walk j).support := by
  have hnone := NilSlot.max_score_nonpath_no_nil T hm ⟨L.index,L.member_not_path⟩
  have hN : (T.walk L.index).toSubgraph.neighborSet r=G.neighborSet r := by
    apply Set.eq_of_subset_of_ncard_le (fun _ h ↦ (T.walk L.index).toSubgraph.adj_sub h)
    change (G.neighborSet r).ncard ≤ ((T.walk L.index).toSubgraph.neighborSet r).ncard
    rw [open_rooted_member_degree T r L hn,←Nat.card_coe_set_eq,hd]
  intro hrj
  have hP := (T.one_defect_other_paths hs L.index L.member_not_path).2 j hji
  obtain ⟨x,hx⟩ := (Set.ncard_pos (Set.toFinite _)).mp (path_neighbor_ncard_pos hP (hnone j) hrj)
  have hxi : (T.walk L.index).toSubgraph.Adj r x := by
    change x ∈ (T.walk L.index).toSubgraph.neighborSet r
    rw [hN]
    exact (T.walk j).toSubgraph.adj_sub hx
  exact Set.disjoint_left.mp (T.disjoint hji)
    (show s(r,x) ∈ (T.walk j).toSubgraph.edgeSet from hx) hxi

lemma cubic_open_root_quota_one (T : TrailFamily G k) (r : V)
    (L : RootedCycleRep T r) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hd : Nat.card (G.neighborSet r)=3) (hn : ¬L.tail.Nil) : T.quota r=1 := by
  classical
  have hr : r ∉ (selectedGraph T (Finset.univ.erase L.index)).support := by
    rintro ⟨x,j,hj,hrx⟩
    exact cubic_open_root_others_avoid T r L hs hm hd hn j (Finset.mem_erase.mp hj).1
      (Walk.mem_support_of_adj_toSubgraph hrx)
  have hrG := path_support_subset_graph_support L.isPath hn r L.tail.start_mem_support
  have hh := NormalRemainder.missing_incidence T r L hs hm hrG hr
  simp only [hd,↓reduceIte,mul_one] at hh
  omega

lemma free_shortest_fully_marked_components_equal
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hG : G.Connected) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : V) (L : RootedCycleRep T r)
    (hmin : ∀ U : TrailFamily G k, ∀ M : RootedCycleRep U r,
      U.score=T.score → M.cycle=L.cycle → ¬M.tail.Nil → L.tail.length ≤ M.tail.length)
    (C D : (MemberComponents.normalGraph T L.index).ConnectedComponent)
    (havC : ∀ j ∈ MemberComponents.componentMembers T L.index C, r ∉ (T.walk j).support)
    (havD : ∀ j ∈ MemberComponents.componentMembers T L.index D, r ∉ (T.walk j).support)
    (hmarkC : ∀ x ∈ (selectedGraph T (MemberComponents.componentMembers T L.index C)).support,
      MarkedPartition (selectedGraph T (MemberComponents.componentMembers T L.index C))
        (MemberComponents.componentMembers T L.index C).card x)
    (hmarkD : ∀ x ∈ (selectedGraph T (MemberComponents.componentMembers T L.index D)).support,
      MarkedPartition (selectedGraph T (MemberComponents.componentMembers T L.index D))
        (MemberComponents.componentMembers T L.index D).card x) : C=D := by
  by_contra hCD
  have hC := free_shortest_fully_marked_component_contains_finish hfail T hG hs r L hmin C havC hmarkC
  have hD := free_shortest_fully_marked_component_contains_finish hfail T hG hs r L hmin D havD hmarkD
  exact Set.disjoint_left.mp (MemberComponents.component_support_disjoint T L.index hCD) hC hD


omit [Fintype V] in
/-- A free minimum in the cubic branch also meets the old quota-fixed
minimum condition, since every comparison with the same quota has an open tail. -/
lemma free_min_implies_quota_fixed_min (T : TrailFamily G k) (r : V)
    (L : RootedCycleRep T r) (hq : T.quota r=1)
    (hmin : ∀ U : TrailFamily G k, ∀ M : RootedCycleRep U r,
      U.score=T.score → M.cycle=L.cycle → ¬M.tail.Nil → L.tail.length ≤ M.tail.length) :
    ∀ U : TrailFamily G k, ∀ M : RootedCycleRep U r,
      U.score=T.score → (∀ x, U.quota x=T.quota x) → M.cycle=L.cycle → L.tail.length ≤ M.tail.length := by
  intro U M hUs hUq hMC
  exact hmin U M hUs hMC (ShortLollipop.quota_one_tail_not_nil U r M ((hUq r).trans hq))

lemma cubic_tight_components_equal {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (r : Fin n)
    (L : RootedCycleRep T r)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hd : Nat.card (G.neighborSet r)=3) (hn : ¬L.tail.Nil)
    (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ M : RootedCycleRep U r,
      U.score=T.score → M.cycle=L.cycle → ¬M.tail.Nil → L.tail.length ≤ M.tail.length)
    (C D : (MemberComponents.normalGraph T L.index).ConnectedComponent)
    (hC : 2*(MemberComponents.componentMembers T L.index C).card=
      (selectedGraph T (MemberComponents.componentMembers T L.index C)).support.ncard+1)
    (hD : 2*(MemberComponents.componentMembers T L.index D).card=
      (selectedGraph T (MemberComponents.componentMembers T L.index D)).support.ncard+1) : C=D := by
  have hm := maximum_of_one_defect_failure hfail T hs
  have hav (E : (MemberComponents.normalGraph T L.index).ConnectedComponent) :
      ∀ j ∈ MemberComponents.componentMembers T L.index E, r ∉ (T.walk j).support := by
    intro j hj
    obtain ⟨hji,_⟩ := (MemberComponents.mem_componentMembers T L.index j E).mp hj
    exact cubic_open_root_others_avoid T r L hs hm hd hn j hji
  apply free_shortest_fully_marked_components_equal hfail T hG hs r L hmin C D (hav C) (hav D)
  · exact tight_normal_group_marked hsmall hfail T hs L.index L.member_not_path _
      (MemberComponents.removed_not_mem T L.index C) (MemberComponents.component_support_connected T L.index C) hC
  · exact tight_normal_group_marked hsmall hfail T hs L.index L.member_not_path _
      (MemberComponents.removed_not_mem T L.index D) (MemberComponents.component_support_connected T L.index D) hD

lemma cubic_tight_component_count {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (r : Fin n)
    (L : RootedCycleRep T r)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hd : Nat.card (G.neighborSet r)=3) (hn : ¬L.tail.Nil)
    (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ M : RootedCycleRep U r,
      U.score=T.score → M.cycle=L.cycle → ¬M.tail.Nil → L.tail.length ≤ M.tail.length) :
    (Finset.univ.filter fun C : (MemberComponents.normalGraph T L.index).ConnectedComponent ↦
      2*(MemberComponents.componentMembers T L.index C).card=
        (selectedGraph T (MemberComponents.componentMembers T L.index C)).support.ncard+1).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro C hC D hD
  exact cubic_tight_components_equal hsmall hG hfail T r L hs hd hn hmin C D
    (Finset.mem_filter.mp hC).2 (Finset.mem_filter.mp hD).2

lemma cubic_free_normal_support {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G k) (r : Fin n) (L : RootedCycleRep T r)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hd : Nat.card (G.neighborSet r)=3) (hn : ¬L.tail.Nil)
    (hcases : L.cycle.length=3 ∨ ∀ x ∈ L.cycle.support, 3 ≤ Nat.card (G.neighborSet x))
    (hmin : ∀ U : TrailFamily G k, ∀ M : RootedCycleRep U r,
      U.score=T.score → M.cycle=L.cycle → ¬M.tail.Nil → L.tail.length ≤ M.tail.length) :
    (selectedGraph T (Finset.univ.erase L.index)).support=({r}ᶜ : Set (Fin n)) := by
  have hq := cubic_open_root_quota_one T r L hs hm hd hn
  exact NormalRemainderOne.cubic_root_normal_support hsmall hG hfail T r L hs hm hd (by omega) hcases
    (free_min_implies_quota_fixed_min T r L hq hmin)

/-- The cubic branch admits its own free-tail optimization. No minimum
quota-energy assertion is transported to the resulting family. -/
lemma cubic_free_certificate {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (r : Fin n)
    (L : RootedCycleRep T r)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hd : Nat.card (G.neighborSet r)=3) (hq : T.quota r ≤ 2)
    (hcases : L.cycle.length=3 ∨ ∀ x ∈ L.cycle.support, 3 ≤ Nat.card (G.neighborSet x)) :
    ∃ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∃ M : RootedCycleRep U r,
      U.score=T.score ∧ M.cycle=L.cycle ∧ ¬M.tail.Nil ∧ U.quota r=1 ∧
      (selectedGraph U (Finset.univ.erase M.index)).support=({r}ᶜ : Set (Fin n)) ∧
      (Finset.univ.filter fun C : (MemberComponents.normalGraph U M.index).ConnectedComponent ↦
        2*(MemberComponents.componentMembers U M.index C).card=
          (selectedGraph U (MemberComponents.componentMembers U M.index C)).support.ncard+1).card ≤ 1 ∧
      ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ N : RootedCycleRep W r,
        W.score=U.score → N.cycle=M.cycle → ¬N.tail.Nil → M.tail.length ≤ N.tail.length := by
  classical
  have hq1 : T.quota r=1 := (QuotaParity.small_root_quota_one_iff T L.hasRoot hq).mpr (by rw [hd]; decide)
  have hn := ShortLollipop.quota_one_tail_not_nil T r L hq1
  obtain ⟨U,M,hUs,hMC,hnM,hmin⟩ := exists_free_shortest_tail T r L hn
  have hsU : U.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by omega
  have hmU := maximum_of_one_defect_failure hfail U hsU
  have hqU := cubic_open_root_quota_one U r M hsU hmU hd hnM
  have hcasesU : M.cycle.length=3 ∨ ∀ x ∈ M.cycle.support, 3 ≤ Nat.card (G.neighborSet x) := by
    rwa [hMC]
  refine ⟨U,M,hUs,hMC,hnM,hqU,?_,?_,hmin⟩
  · exact cubic_free_normal_support hsmall hG hfail U r M hsU hmU hd hnM hcasesU hmin
  · exact cubic_tight_component_count hsmall hG hfail U r M hsU hd hnM hmin

end Erdos583FreeTailGroupsDevelopment
