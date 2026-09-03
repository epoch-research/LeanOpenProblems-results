import Submission.ShortestTailBridges

/-! A free shortest two-edge triangle tail leaves at most two normal components. -/
namespace Erdos583ShortTriangleComponentsDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583Work.MemberExpansion Erdos583Work.MemberComponents
open Erdos583ShortestTailBridgesDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma component_single_anchor_bridge {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) (C : (normalGraph T i).ConnectedComponent)
    {u v : V} (hu : u ∈ (selectedGraph T (componentMembers T i C)).support)
    (hv : v ∉ (selectedGraph T (componentMembers T i C)).support)
    (hAdj : (T.walk i).toSubgraph.Adj u v)
    (hanchor : ∀ x ∈ (selectedGraph T (componentMembers T i C)).support,
      x ∈ (T.walk i).support → x=u)
    (hleaf : ∀ y, (T.walk i).toSubgraph.Adj u y → y=v) : G.IsBridge s(u,v) := by
  apply ContiguousRegion.unique_crossing_bridge (selectedGraph T (componentMembers T i C)).support
    ((T.walk i).toSubgraph.adj_sub hAdj) hu hv
  intro x hx y hy hxy
  obtain ⟨j,hj⟩ := (T.cover s(x,y)).mp hxy
  by_cases hji : j=i
  · subst j
    have hxu := hanchor x hx (Walk.mem_support_of_adj_toSubgraph hj)
    exact ⟨hxu,hleaf y (hxu ▸ hj)⟩
  · obtain ⟨z,l,hl,hxl⟩ := hx
    obtain ⟨hli,hlC⟩ := (mem_componentMembers T i l C).mp hl
    have he := same_component_of_intersection T i hli hji
      (Walk.mem_support_of_adj_toSubgraph hxl) (Walk.mem_support_of_adj_toSubgraph hj)
    have hjC : j ∈ componentMembers T i C := (mem_componentMembers T i j C).mpr
      ⟨hji,he.symm.trans hlC⟩
    exact (hy ⟨x,j,hjC,hj.symm⟩).elim

lemma short_triangle_component_contains_root_or_penultimate {n k : ℕ}
    (hsmall : VertexCritical.SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : Fin n) (L : RootedCycleRep T r)
    (hmin : ∀ U : TrailFamily G k, ∀ M : RootedCycleRep U r,
      U.score=T.score → M.cycle=L.cycle → L.tail.length ≤ M.tail.length)
    (hcycle : L.cycle.length=3) {s : Fin n} (hrs : G.Adj r s) (hst : G.Adj s L.finish)
    (hS : L.tail=Walk.cons hrs (Walk.cons hst Walk.nil))
    (C : (normalGraph T L.index).ConnectedComponent) :
    r ∈ (selectedGraph T (componentMembers T L.index C)).support ∨
      s ∈ (selectedGraph T (componentMembers T L.index C)).support := by
  classical
  let K := (selectedGraph T (componentMembers T L.index C)).support
  have htail : L.tail.length=2 := by rw [hS]; rfl
  have hn : ¬L.tail.Nil := fun h ↦ by have := Walk.nil_iff_length_eq.mp h; omega
  have htr := (ContiguousRegion.path_ends_ne L.tail L.isPath hn).symm
  have hnone := NilSlot.max_score_nonpath_no_nil T hm ⟨L.index,L.member_not_path⟩
  have hhitroot {x : Fin n} (hxK : x ∈ K) (hxC : x ∈ L.cycle.support) : r ∈ K := by
    obtain ⟨y,j,hj,hxy⟩ := hxK
    have hji := (mem_componentMembers T L.index j C).mp hj |>.1
    have hrj : r ∈ (T.walk j).support := by
      by_contra hrj
      exact TriangleTailTwo.maximum_two_tail_triangle_no_outside_intersection T r L hs hm hcycle htail
        j hji.symm hrj ⟨x,hxC,Walk.mem_support_of_adj_toSubgraph hxy⟩
    dsimp only [K]
    rw [selected_support_eq T _ (fun j _ ↦ hnone j)]
    exact ⟨j,hj,hrj⟩
  by_contra hnmem
  have hr : r ∉ K := fun h ↦ hnmem (Or.inl h)
  have hsm : s ∉ K := fun h ↦ hnmem (Or.inr h)
  have hanchor : ∀ x ∈ K, x ∈ (T.walk L.index).support → x=L.finish := by
    intro x hx hxL
    rw [←Walk.mem_verts_toSubgraph,L.subgraph,Walk.mem_verts_toSubgraph,Walk.mem_support_append_iff] at hxL
    rcases hxL with hxC | hxS
    · exact (hr (hhitroot hx hxC)).elim
    · rw [hS] at hxS
      simp only [Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at hxS
      rcases hxS with rfl | rfl | hx
      · exact (hr hx).elim
      · exact (hsm hx).elim
      · exact hx
  obtain ⟨x,hxL,hxK⟩ := component_meets_removed T hG L.index hnone C
  have ht : L.finish ∈ K := hanchor x hxK ((T.walk L.index).mem_verts_toSubgraph.mp hxL) ▸ hxK
  have htC : L.finish ∉ L.cycle.support := fun h ↦ htr (L.inter L.finish h L.tail.end_mem_support)
  have hAdj : (T.walk L.index).toSubgraph.Adj L.finish s := by
    rw [L.subgraph,Walk.toSubgraph_append]
    apply Or.inr
    rw [hS]
    change s(L.finish,s) ∈ (Walk.cons hrs (Walk.cons hst Walk.nil)).toSubgraph.edgeSet
    simp [Sym2.eq_swap]
  have hleaf (y : Fin n) (hy : (T.walk L.index).toSubgraph.Adj L.finish y) : y=s := by
    rw [L.subgraph,Walk.toSubgraph_append] at hy
    rcases hy with hy | hy
    · exact (htC (Walk.mem_support_of_adj_toSubgraph hy)).elim
    · rw [hS] at hy
      change s(L.finish,y) ∈ (Walk.cons hrs (Walk.cons hst Walk.nil)).toSubgraph.edgeSet at hy
      simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false,Sym2.eq_iff] at hy
      have hts := hst.ne.symm
      aesop
  have hbridge := component_single_anchor_bridge T L.index C ht hsm hAdj hanchor hleaf
  have hform : L.tail=(Walk.cons hrs Walk.nil).append (Walk.cons hst Walk.nil) := by rw [hS]; rfl
  exact shortest_tail_no_internal_bridge hsmall hG hfail T hs r L hmin
    (Walk.cons hrs Walk.nil) hst Walk.nil hform hrs.ne.symm (by simpa only [Sym2.eq_swap] using hbridge)

lemma short_triangle_normal_component_count_le_two {n k : ℕ}
    (hsmall : VertexCritical.SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : Fin n) (L : RootedCycleRep T r)
    (hmin : ∀ U : TrailFamily G k, ∀ M : RootedCycleRep U r,
      U.score=T.score → M.cycle=L.cycle → L.tail.length ≤ M.tail.length)
    (hcycle : L.cycle.length=3) (htail : L.tail.length=2) :
    Nat.card (normalGraph T L.index).ConnectedComponent ≤ 2 := by
  classical
  obtain ⟨s,hrs,hst,hS⟩ := TriangleTailTwo.two_edge_form L.tail htail
  let K (C : (normalGraph T L.index).ConnectedComponent) :=
    (selectedGraph T (componentMembers T L.index C)).support
  have hhit (C) : r ∈ K C ∨ s ∈ K C :=
    short_triangle_component_contains_root_or_penultimate hsmall hG hfail T hs hm r L hmin hcycle hrs hst hS C
  let f : (normalGraph T L.index).ConnectedComponent → Bool := fun C ↦ decide (r ∈ K C)
  have hf : Function.Injective f := by
    intro C D he
    by_contra hCD
    have hd := Set.disjoint_left.mp (component_support_disjoint T L.index hCD)
    by_cases hrC : r ∈ K C
    · have hrD : r ∈ K D := by
        apply of_decide_eq_true
        simpa only [f,hrC,decide_true] using he.symm
      exact hd hrC hrD
    · have hrD : r ∉ K D := by
        apply of_decide_eq_false
        simpa only [f,hrC,decide_false] using he.symm
      exact hd ((hhit C).resolve_left hrC) ((hhit D).resolve_left hrD)
  simpa using Nat.card_le_card_of_injective f hf

end Erdos583ShortTriangleComponentsDevelopment
