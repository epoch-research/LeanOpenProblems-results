import Submission.CubicCutReachability

/-! An odd external attachment cannot be separated from the root by a cubic-pair shortcut. -/
namespace Erdos583ShortTriangleCubicCutDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583ShortTriangleIncidenceDevelopment Erdos583ShortTriangleEndpointTransferDevelopment
open Erdos583MixedTriangleTerminalExclusionDevelopment Erdos583CubicCutReachabilityDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma short_triangle_cubic_cut_not_odd {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hc : L.cycle.length=3)
    (ht : L.tail.length=1 ∨ L.tail.length=2)
    {x y a b d : V} (hrx : r ≠ x) (hry : r ≠ y) (hbx : b ≠ x) (hay : a ≠ y)
    (hyC : y ∈ L.cycle.support) (hyb : G.Adj y b)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=b)
    (hra : (puncture (G.deleteEdges {s(a,b)}) ({x,y} : Set V)).Reachable r a)
    (hnrb : ¬(puncture (G.deleteEdges {s(a,b)}) ({x,y} : Set V)).Reachable r b)
    (i : Fin k) (hiL : i ≠ L.index) (P : G.Walk y d) (hP : P.IsPath)
    (hPi : (T.walk i).toSubgraph=P.toSubgraph) (hybP : s(y,b) ∈ P.edges) :
    ¬Odd (Nat.card (G.neighborSet b)) := by
  classical
  intro hbodd
  have hyi : y ∈ (T.walk i).support := by
    rw [←Walk.mem_verts_toSubgraph,hPi,Walk.mem_verts_toSubgraph]
    exact P.start_mem_support
  have hrP := short_triangle_member_contains_root T hs hm r L hc ht i hyC hyi
  rw [←Walk.mem_verts_toSubgraph,hPi,Walk.mem_verts_toSubgraph] at hrP
  obtain ⟨A,hPA⟩ := path_cons_of_start_edge P hP hyb hybP
  have hyA : y ∉ A.support := (Walk.cons_isPath_iff hyb A).mp (hPA ▸ hP) |>.2
  have hrA : r ∈ A.support := by
    rw [hPA,Walk.support_cons,List.mem_cons] at hrP
    exact hrP.resolve_left hry
  have hybA : s(y,b) ∉ A.edges := fun h ↦ hyA (A.fst_mem_support_of_mem_edges h)
  have habP : s(a,b) ∈ P.edges := by
    by_contra hh
    have habA : s(a,b) ∉ A.edges := by
      intro h
      apply hh
      rw [hPA,Walk.edges_cons,List.mem_cons]
      exact Or.inr h
    exact cubic_cut_walk_separation hrx hry hbx hyb.ne.symm hNx hNy hra hnrb
      A habA hybA hrA A.start_mem_support
  have hseparate (j : Fin k) (hji : j ≠ i) (hbj : b ∈ (T.walk j).support) : r ∉ (T.walk j).support := by
    intro hrj
    have hnot {e : Sym2 V} (he : e ∈ P.edges) : e ∉ (T.walk j).edges := by
      intro hj
      apply Set.disjoint_left.mp (T.disjoint hji.symm)
      · rw [hPi]; exact P.mem_edges_toSubgraph.mpr he
      · exact (T.walk j).mem_edges_toSubgraph.mpr hj
    exact cubic_cut_walk_separation hrx hry hbx hyb.ne.symm hNx hNy hra hnrb
      (T.walk j) (hnot habP) (hnot hybP) hrj hbj
  obtain ⟨j,hjb⟩ := DeletionEndpoint.endpoint_of_positive_quota T ((QuotaParity.quota_odd_iff T b).mpr hbodd).pos
  have hji : j ≠ i := by
    intro hji
    subst j
    obtain ⟨e,Q,hQ,hQe⟩ := orient_path_at_endpoint (T.walk i)
      ((T.one_defect_other_paths hs L.index L.member_not_path).2 i hiL) hjb
    have hbyQ : s(b,y) ∈ Q.edges := by
      rw [←Walk.mem_edges_toSubgraph,←hQe,hPi,Walk.mem_edges_toSubgraph]
      simpa only [Sym2.eq_swap] using hybP
    have hbaQ : s(b,a) ∈ Q.edges := by
      rw [←Walk.mem_edges_toSubgraph,←hQe,hPi,Walk.mem_edges_toSubgraph]
      simpa only [Sym2.eq_swap] using habP
    exact hay ((hQ.eq_snd_of_mem_edges hbaQ).trans (hQ.eq_snd_of_mem_edges hbyQ).symm)
  have hbj : b ∈ (T.walk j).support := hjb.elim
    (fun h ↦ h ▸ (T.walk j).start_mem_support) (fun h ↦ h ▸ (T.walk j).end_mem_support)
  have hrj := hseparate j hji hbj
  have hjL : j ≠ L.index := by
    intro hh
    subst j
    apply hrj
    rw [←Walk.mem_verts_toSubgraph,L.subgraph,Walk.mem_verts_toSubgraph,Walk.mem_support_append_iff]
    exact Or.inl L.cycle.start_mem_support
  obtain ⟨e,Q,hQ,hQe⟩ := orient_path_at_endpoint (T.walk j)
    ((T.one_defect_other_paths hs L.index L.member_not_path).2 j hjL) hjb
  have hrQ : r ∉ Q.support := by
    intro hh
    apply hrj
    rwa [←Walk.mem_verts_toSubgraph,hQe,Walk.mem_verts_toSubgraph]
  exact short_triangle_terminal_transfer T hs hm r L hc ht i j hji.symm hiL hjL
    hyb A Q (hPA ▸ hP) hQ (hPi.trans (congrArg Walk.toSubgraph hPA)) hQe hyC hry.symm hrQ

end Erdos583ShortTriangleCubicCutDevelopment
