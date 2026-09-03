import Submission.GlobalTailDefect

/-! Exchange the tail with a normal member attached at exactly one cycle
endpoint. Unlike a fixed-root tail comparison, this may change the root. -/
namespace Erdos583GlobalTailExchangeDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583GeneralPairEndpointsDevelopment Erdos583GlobalTailDefectDevelopment
open Erdos583UnifiedMinimalDefectDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma exchange_tail_at_cycle_endpoint {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (r : V) (L : RootedCycleRep T r)
    (j : Fin k) (hij : L.index ≠ j) {s b : V} (P : G.Walk s b)
    (hp : P.IsPath) (hP : (T.walk j).toSubgraph=P.toSubgraph)
    (hs : s ∈ L.cycle.support)
    (hinter : ∀ x ∈ L.cycle.support, x ∈ P.support → x=s) :
    ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U s,
      U.score=T.score ∧ M.cycle.length=L.cycle.length ∧ M.tail.length=P.length ∧
      (U.walk j).toSubgraph=L.tail.toSubgraph ∧
      ∀ i, i ≠ L.index → i ≠ j → (U.walk i).toSubgraph=(T.walk i).toSubgraph := by
  let C := L.cycle.rotate hs
  have hC : C.IsCycle := L.isCycle.rotate hs
  have hCE : C.toSubgraph=L.cycle.toSubgraph := L.cycle.toSubgraph_rotate hs
  have hCP (x) (hx : x ∈ C.support) (hxP : x ∈ P.support) : x=s := by
    apply hinter x _ hxP
    rwa [←Walk.mem_verts_toSubgraph,hCE,Walk.mem_verts_toSubgraph] at hx
  have hCT : Disjoint C.toSubgraph.edgeSet L.tail.toSubgraph.edgeSet := by
    rw [hCE]
    exact edge_disjoint_of_one_common_vertex L.cycle L.tail L.inter
  have hPT : Disjoint P.toSubgraph.edgeSet L.tail.toSubgraph.edgeSet := by
    apply (T.disjoint hij.symm).mono
    · rw [hP]
    · rw [L.subgraph,Walk.toSubgraph_append,Subgraph.edgeSet_sup]
      exact Set.subset_union_right
  have hnew : (C.append P).IsTrail := trail_append_of_disjoint hC.isTrail hp.isTrail
    (edge_disjoint_of_one_common_vertex C P hCP)
  have hd : Disjoint (C.append P).toSubgraph.edgeSet L.tail.toSubgraph.edgeSet := by
    rw [Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    exact disjoint_sup_left.mpr ⟨hCT,hPT⟩
  have hc : (C.append P).toSubgraph.edgeSet ∪ L.tail.toSubgraph.edgeSet=
      (T.walk L.index).toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet := by
    rw [L.subgraph,hP,Walk.toSubgraph_append,Walk.toSubgraph_append,
      Subgraph.edgeSet_sup,Subgraph.edgeSet_sup,hCE]
    ext e
    simp only [Set.mem_union]
    tauto
  obtain ⟨U,hUi,hUj,hrest,hscore,hUa,hUb,_,_⟩ := replace_two_endpoints T L.index j hij
    s b r L.finish (C.append P) L.tail hnew L.isPath.isTrail hd hc
  have hCL : C.length=L.cycle.length := by
    rw [←trail_edgeSet_ncard C hC.isTrail,hCE,trail_edgeSet_ncard L.cycle L.isCycle.isTrail]
  have hUs : U.score=T.score := by
    rw [L.subgraph,hP,lollipop_vertex_card L.cycle L.isCycle L.tail L.isPath L.inter,
      lollipop_vertex_card C hC P hp hCP,(walk_vertex_ncard_eq_iff _).mpr hp,
      (walk_vertex_ncard_eq_iff _).mpr L.isPath] at hscore
    simp only [Walk.length_append,hCL] at hscore
    omega
  let M : RootedCycleRep U s := ⟨L.index,b,hUa,hUb,C,P,hC,hp,hCP,hUi⟩
  exact ⟨U,M,hUs,hCL,rfl,hUj,hrest⟩

lemma GloballyTailOptimized.tail_le_one_touch_member {n : ℕ}
    {G : SimpleGraph (Fin n)} (D : GloballyTailOptimized G)
    (j : Fin (budget n)) (hij : D.rep.index ≠ j) {s b : Fin n} (P : G.Walk s b)
    (hp : P.IsPath) (hP : (D.family.walk j).toSubgraph=P.toSubgraph)
    (hs : s ∈ D.rep.cycle.support)
    (hinter : ∀ x ∈ D.rep.cycle.support, x ∈ P.support → x=s) :
    D.rep.tail.length ≤ P.length := by
  obtain ⟨U,M,hUs,hMC,hMT,_,_⟩ := exchange_tail_at_cycle_endpoint D.family D.root D.rep
    j hij P hp hP hs hinter
  have hh := D.global_tail_minimum U s M hUs hMC
  rwa [hMT] at hh

lemma one_edge_cycle_carrier_forces_one_tail (F : MinimalFailure)
    (D : GloballyTailOptimized F.graph) (j : Fin (budget F.order)) (hij : D.rep.index ≠ j)
    {s b : Fin F.order} (h : F.graph.Adj s b)
    (hP : (D.family.walk j).toSubgraph=(Walk.cons h Walk.nil).toSubgraph)
    (hs : s ∈ D.rep.cycle.support) (hb : b ∉ D.rep.cycle.support) :
    D.rep.tail.length=1 := by
  have hlen := GloballyTailOptimized.tail_le_one_touch_member D j hij (Walk.cons h Walk.nil)
    (by simp [Walk.cons_isPath_iff,h.ne]) hP hs (by
      intro x hxC hxP
      rcases (show x=s ∨ x=b from by simpa only [Walk.support_cons,Walk.support_nil,
        List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using hxP) with hx|hx
      · exact hx
      · exact (hb (hx ▸ hxC)).elim)
  have hpos := Walk.not_nil_iff_lt_length.mp (tail_not_nil F D.toOptimizedDefect)
  simp only [Walk.length_cons,Walk.length_nil] at hlen
  omega

end Erdos583GlobalTailExchangeDevelopment
