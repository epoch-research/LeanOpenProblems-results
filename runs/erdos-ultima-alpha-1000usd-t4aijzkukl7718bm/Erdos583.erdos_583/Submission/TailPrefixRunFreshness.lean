import Submission.RunCompressionData

/-! Fresh shortcuts for runs in a prefix of the optimized tail. -/
namespace Erdos583TailPrefixRunFreshnessDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open Erdos583Work.QuotaTrails Erdos583Work.LollipopEar
open Erdos583Work.MemberExpansion Erdos583Work.MemberComponents
open Erdos583CycleRunIntervalsDevelopment Erdos583PathRunIntervalsDevelopment
open Erdos583PathIntervalsDevelopment Erdos583RunCompressionDataDevelopment
open Erdos583LongTailEarDevelopment Erdos583NormalComponentComplementDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false
variable {V : Type*} {G : SimpleGraph V} {a b w : V}

lemma path_append_support_inter (W : G.Walk a w) (Q : G.Walk w b)
    (hp : (W.append Q).IsPath) {z : V} (hzW : z ∈ W.support) (hzQ : z ∈ Q.support) : z=w := by
  by_contra hzw
  exact hp.ne_of_mem_support_of_append hzw hzW hzQ rfl

lemma prefix_run_shortcut_not_tail (W : G.Walk a w) (Q : G.Walk w b)
    (hp : (W.append Q).IsPath) (S : Set V) (p : RunIndex W) (hr : p ∈ runs W S) :
    s(runStart W p,runFinish W p) ∉ (W.append Q).edges := by
  intro he
  rw [Walk.edges_append] at he
  rcases List.mem_append.mp he with he|he
  · exact run_shortcut_not_path_edge W hp.of_append_left S ((mem_runs W S p).mp hr) he
  · have hadj := Q.mem_edges_toSubgraph.mpr he
    have haQ := Walk.mem_support_of_adj_toSubgraph hadj
    have hbQ := Walk.mem_support_of_adj_toSubgraph hadj.symm
    have haW := W.getVert_mem_support p.val.1.val
    have hbW := W.getVert_mem_support p.val.2.val
    exact run_endpoint_ne W hp.of_append_left S ((mem_runs W S p).mp hr)
      ((path_append_support_inter W Q hp haW haQ).trans (path_append_support_inter W Q hp hbW hbQ).symm)

lemma prefix_tail_runs_fresh [Fintype V] {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (root : V) (L : RootedCycleRep T root)
    (hmin : ∀ U : TrailFamily G k, ∀ M : RootedCycleRep U root,
      U.score=T.score → (∀ x, U.quota x=T.quota x) → M.cycle=L.cycle → L.tail.length ≤ M.tail.length)
    (A : (normalGraph T L.index).ConnectedComponent) (S : Set V)
    (hS : S ⊆ (selectedGraph T (componentMembers T L.index A)).support)
    {w : V} (W : G.Walk root w) (Q : G.Walk w L.finish) (hform : L.tail=W.append Q) :
    let F := selectedGraph T (Finset.univ \ componentMembers T L.index A)
    ∀ p ∈ runs W S, ¬(within F Sᶜ).Adj (runStart W p) (runFinish W p) := by
  dsimp only
  have hp : (W.append Q).IsPath := hform ▸ L.isPath
  intro p hpr hh
  have hr := (mem_runs W S p).mp hpr
  have hab := run_endpoint_ne W hp.of_append_left S hr
  obtain ⟨j,hj,hxy⟩ := hh.1
  have hji : j ≠ L.index := by
    intro he
    subst j
    rw [L.subgraph,Walk.toSubgraph_append,Subgraph.sup_adj] at hxy
    rcases hxy with hxy|hxy
    · have haC := Walk.mem_support_of_adj_toSubgraph hxy
      have hbC := Walk.mem_support_of_adj_toSubgraph hxy.symm
      have haT : runStart W p ∈ L.tail.support := by
        rw [hform,Walk.mem_support_append_iff]
        exact Or.inl (W.getVert_mem_support _)
      have hbT : runFinish W p ∈ L.tail.support := by
        rw [hform,Walk.mem_support_append_iff]
        exact Or.inl (W.getVert_mem_support _)
      exact hab ((L.inter _ haC haT).trans (L.inter _ hbC hbT).symm)
    · rw [hform] at hxy
      exact prefix_run_shortcut_not_tail W Q hp S p hpr ((W.append Q).mem_edges_toSubgraph.mp hxy)
  have hav : ∀ z ∈ (runPath W p).support, z ≠ runStart W p → z ≠ runFinish W p →
      z ∉ (T.walk j).support := by
    intro z hz hza hzb hzj
    exact Set.disjoint_left.mp (outside_member_avoids T L.index A hji (Finset.mem_sdiff.mp hj).2)
      ((T.walk j).mem_verts_toSubgraph.mpr hzj) (hS (hr.internal_mem W S hz hza hzb))
  have hsplit : L.tail=(W.take p.val.1.val).append ((runPath W p).append ((W.drop p.val.2.val).append Q)) := by
    calc
      L.tail = W.append Q := hform
      _ = ((W.take p.val.1.val).append ((runPath W p).append (W.drop p.val.2.val))).append Q :=
        congrArg (fun Z ↦ Z.append Q) (split_interval W _ hr.2.1)
      _ = _ := by simp only [Walk.append_assoc]
  exact no_long_tail_ear T root L hs hmin j hji.symm (W.take p.val.1.val) (runPath W p)
    ((W.drop p.val.2.val).append Q) ((T.walk j).toSubgraph.adj_sub hxy) hsplit
    (by rw [runPath,interval_length W _ hr.2.1]; have := p.property; omega)
    ((T.walk j).mem_edges_toSubgraph.mp hxy) hav

end Erdos583TailPrefixRunFreshnessDevelopment
