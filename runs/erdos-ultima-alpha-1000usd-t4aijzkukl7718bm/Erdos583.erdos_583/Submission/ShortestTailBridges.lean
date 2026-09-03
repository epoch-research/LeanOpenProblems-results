import Submission.ShortTriangleRootExclusion

/-! In a free shortest tail, a bridge can occur only as the first edge. -/
namespace Erdos583ShortestTailBridgesDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583RootQuotaTailBoundDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma bridge_separates_suffix {V : Type*} {G : SimpleGraph V} {w v t b : V}
    (e : G.Adj w v) (he : G.IsBridge s(w,v)) (B : G.Walk v t) (P : G.Walk w b)
    (hB : s(w,v) ∉ B.edges) (hP : s(w,v) ∉ P.edges) :
    ∀ x ∈ (Walk.cons e B).support, x ∈ P.support → x=w := by
  intro x hx hxP
  rcases List.mem_cons.mp hx with hx | hxB
  · exact hx
  · let Q := (P.takeUntil x hxP).append (B.takeUntil x hxB).reverse
    have hedge := (isBridge_iff_adj_and_forall_walk_mem_edges.mp he).2 Q
    simp only [Q,Walk.edges_append,Walk.edges_reverse,List.mem_append,List.mem_reverse] at hedge
    exact hedge.elim
      (fun h ↦ (hP (P.edges_takeUntil_subset hxP h)).elim)
      (fun h ↦ (hB (B.edges_takeUntil_subset hxB h)).elim)

lemma shortest_tail_no_internal_bridge {n k : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : Fin n) (L : RootedCycleRep T r)
    (hmin : ∀ U : TrailFamily G k, ∀ M : RootedCycleRep U r,
      U.score=T.score → M.cycle=L.cycle → L.tail.length ≤ M.tail.length)
    {w v : Fin n} (R : G.Walk r w) (e : G.Adj w v) (B : G.Walk v L.finish)
    (hform : L.tail=R.append (Walk.cons e B)) (hwr : w ≠ r) : ¬G.IsBridge s(w,v) := by
  intro hbridge
  have hodd := (BridgeParityReduction.bridge_endpoints_odd_of_failure hsmall hG hfail hbridge).1
  have hq := ((QuotaParity.quota_odd_iff T w).mpr hodd).pos
  obtain ⟨j,hj⟩ := DeletionEndpoint.endpoint_of_positive_quota T hq
  have hp := hform ▸ L.isPath
  have hwb : w ≠ L.finish := by
    intro he
    exact TriangleAbsorption.append_cons_support_disjoint R e B hp w R.end_mem_support (he ▸ B.end_mem_support)
  have hij : L.index ≠ j := by
    rintro rfl
    rcases hj with hj | hj
    · exact hwr (hj.trans L.start_eq)
    · exact hwb (hj.trans L.finish_eq)
  have hpj := (T.one_defect_other_paths hs L.index L.member_not_path).2 j hij.symm
  have hpath : ∃ b, ∃ P : G.Walk w b, P.IsPath ∧ (T.walk j).toSubgraph=P.toSubgraph := by
    rcases hj with hj | hj
    · exact simple_member_from_root_slot T w (j,true) hj.symm hpj
    · exact simple_member_from_root_slot T w (j,false) hj.symm hpj
  obtain ⟨b,P,hP,hPe⟩ := hpath
  have heL : s(w,v) ∈ (T.walk L.index).toSubgraph.edgeSet := by
    rw [L.subgraph,hform]; simp
  have heP : s(w,v) ∉ P.edges := fun he ↦
    Set.disjoint_left.mp (T.disjoint hij) heL (hPe.symm ▸ P.mem_edges_toSubgraph.mpr he)
  have heB : s(w,v) ∉ B.edges := (Walk.isTrail_cons e B).mp hp.of_append_right.isTrail |>.2
  obtain ⟨U,M,hUs,hMC,_,hML⟩ := FreeTailGroups.shorten_tail_at_marked_path T r L hs j hij R
    (Walk.cons e B) hform P hP hPe (bridge_separates_suffix e hbridge B P heB heP)
  have hh := hmin U M hUs hMC
  rw [hML,hform,Walk.length_append,Walk.length_cons] at hh
  omega

lemma shortest_tail_last_bridge_length_one {n k : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : Fin n) (L : RootedCycleRep T r)
    (hmin : ∀ U : TrailFamily G k, ∀ M : RootedCycleRep U r,
      U.score=T.score → M.cycle=L.cycle → L.tail.length ≤ M.tail.length)
    {w : Fin n} (R : G.Walk r w) (e : G.Adj w L.finish)
    (hform : L.tail=R.concat e) (he : G.IsBridge s(w,L.finish)) : L.tail.length=1 := by
  have hform' : L.tail=R.append (Walk.cons e Walk.nil) := by rw [hform,Walk.concat_eq_append]
  have hwr : w=r := by
    by_contra hwr
    exact shortest_tail_no_internal_bridge hsmall hG hfail T hs r L hmin R e Walk.nil hform' hwr he
  subst w
  have hR : R=Walk.nil := (Walk.isPath_iff_eq_nil R).mp ((hform' ▸ L.isPath).of_append_left)
  rw [hform',hR]; rfl

end Erdos583ShortestTailBridgesDevelopment
