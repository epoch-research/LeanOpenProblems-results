import Submission.PathRunIntervals

/-! Tail-run shortcuts are fresh at a shortest tail with the cycle fixed. -/
namespace Erdos583TailRunFreshnessDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583Work.MemberExpansion Erdos583Work.MemberComponents Erdos583Work.BridgeGlue
open Erdos583CycleRunIntervalsDevelopment Erdos583PathRunIntervalsDevelopment
open Erdos583PathIntervalsDevelopment Erdos583LongTailEarDevelopment
open Erdos583NormalComponentComplementDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma subset_tail_runs_fresh {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (root : V) (L : RootedCycleRep T root)
    (hmin : ∀ U : TrailFamily G k, ∀ M : RootedCycleRep U root,
      U.score=T.score → (∀ x, U.quota x=T.quota x) → M.cycle=L.cycle → L.tail.length ≤ M.tail.length)
    (A : (normalGraph T L.index).ConnectedComponent)
    (S : Set V) (hS : S ⊆ (selectedGraph T (componentMembers T L.index A)).support) :
    let F := selectedGraph T (Finset.univ \ componentMembers T L.index A)
    ∀ p ∈ runs L.tail S, ¬(within F Sᶜ).Adj (runStart L.tail p) (runFinish L.tail p) := by
  dsimp only
  intro p hp hh
  have hr := (mem_runs L.tail S p).mp hp
  have hab := run_endpoint_ne L.tail L.isPath S hr
  obtain ⟨j,hj,hxy⟩ := hh.1
  have hji : j ≠ L.index := by
    intro he
    subst j
    rw [L.subgraph,Walk.toSubgraph_append,Subgraph.sup_adj] at hxy
    rcases hxy with hxy|hxy
    · have haC := Walk.mem_support_of_adj_toSubgraph hxy
      have hbC := Walk.mem_support_of_adj_toSubgraph hxy.symm
      have haT := L.tail.getVert_mem_support p.val.1.val
      have hbT := L.tail.getVert_mem_support p.val.2.val
      exact hab ((L.inter _ haC haT).trans (L.inter _ hbC hbT).symm)
    · exact run_shortcut_not_path_edge L.tail L.isPath S hr (L.tail.mem_edges_toSubgraph.mp hxy)
  have hav : ∀ z ∈ (runPath L.tail p).support, z ≠ runStart L.tail p → z ≠ runFinish L.tail p →
      z ∉ (T.walk j).support := by
    intro z hz hza hzb hzj
    exact Set.disjoint_left.mp (outside_member_avoids T L.index A hji (Finset.mem_sdiff.mp hj).2)
      ((T.walk j).mem_verts_toSubgraph.mpr hzj) (hS (hr.internal_mem L.tail S hz hza hzb))
  exact no_long_tail_ear T root L hs hmin j hji.symm (L.tail.take p.val.1.val) (runPath L.tail p)
    (L.tail.drop p.val.2.val) ((T.walk j).toSubgraph.adj_sub hxy)
    (split_interval L.tail _ hr.2.1)
    (by rw [runPath,interval_length L.tail _ hr.2.1]; have := p.property; omega)
    ((T.walk j).mem_edges_toSubgraph.mp hxy) hav

end Erdos583TailRunFreshnessDevelopment
