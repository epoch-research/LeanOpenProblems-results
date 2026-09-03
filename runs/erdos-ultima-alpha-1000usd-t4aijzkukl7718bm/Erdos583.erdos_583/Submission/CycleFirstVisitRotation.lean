import Submission.FreeRootCycleMinimum

/-! Cycle-edge rotation at a path's first visit, retaining its exterior prefix. -/
namespace Erdos583CycleFirstVisitRotationDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583Work.LollipopEar
open Erdos583CycleEndpointRotationDevelopment Erdos583GeneralPairEndpointsDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma cycle_first_visit_rotation {V : Type*} {G : SimpleGraph V} {a u v w b : V}
    (h : G.Adj u v) (Q : G.Walk v u) (hC : (Walk.cons h Q).IsCycle)
    (A : G.Walk a u) (R : G.Walk u w) (f : G.Adj w v) (B : G.Walk v b)
    (hp : (A.append (R.append (Walk.cons f B))).IsPath)
    (hA : ∀ x ∈ A.support, x ∈ (Walk.cons h Q).support → x=u)
    (hd : Disjoint (Walk.cons h Q).toSubgraph.edgeSet
      (A.append (R.append (Walk.cons f B))).toSubgraph.edgeSet) :
    (Q.append A.reverse).IsPath ∧
      (Walk.cons f (Q.append A.reverse)).IsTrail ∧
      (R.reverse.append (Walk.cons h B)).IsPath ∧
      Disjoint (Walk.cons f (Q.append A.reverse)).toSubgraph.edgeSet
        (R.reverse.append (Walk.cons h B)).toSubgraph.edgeSet ∧
      (Walk.cons f (Q.append A.reverse)).toSubgraph.edgeSet ∪
          (R.reverse.append (Walk.cons h B)).toSubgraph.edgeSet=
        (Walk.cons h Q).toSubgraph.edgeSet ∪
          (A.append (R.append (Walk.cons f B))).toSubgraph.edgeSet ∧
      w ≠ u ∧ w ∉ A.support := by
  classical
  have hQ := (Walk.cons_isCycle_iff Q h).mp hC |>.1
  have hQA : (Q.append A.reverse).IsPath := by
    apply path_append_of_support_intersection hQ hp.of_append_left.reverse
    intro x hxQ hxA
    exact hA x (by simpa using hxA) (List.mem_cons_of_mem _ hxQ)
  have hd' := hd
  rw [Walk.toSubgraph_append,Subgraph.edgeSet_sup] at hd'
  have hdCA := (disjoint_sup_right.mp hd').1
  have hdCD := (disjoint_sup_right.mp hd').2
  obtain ⟨hY,hX,hYX,hcover,_,_,hwu⟩ :=
    cycle_endpoint_rotation h Q hC R f B hp.of_append_right hdCD
  have hDA := (RootedTailSystem.append_trail_disjoint hp.isTrail).symm
  have hnewA : Disjoint
      ((Walk.cons f Q).toSubgraph.edgeSet ∪
        (R.reverse.append (Walk.cons h B)).toSubgraph.edgeSet) A.toSubgraph.edgeSet := by
    rw [hcover]
    exact disjoint_sup_left.mpr ⟨hdCA,hDA⟩
  have hYA := (disjoint_sup_left.mp hnewA).1
  have hXA := (disjoint_sup_left.mp hnewA).2
  have hwhole : (Walk.cons f (Q.append A.reverse)).IsTrail := by
    rw [←Walk.cons_append]
    apply trail_append_of_disjoint hY hp.of_append_left.reverse.isTrail
    simpa only [Walk.toSubgraph_reverse] using hYA
  refine ⟨hQA,hwhole,hX,?_,?_,hwu,?_⟩
  · rw [←Walk.cons_append,Walk.toSubgraph_append,Subgraph.edgeSet_sup,Walk.toSubgraph_reverse]
    exact disjoint_sup_left.mpr ⟨hYX,hXA.symm⟩
  · rw [←Walk.cons_append,Walk.toSubgraph_append,Subgraph.edgeSet_sup,Walk.toSubgraph_reverse]
    rw [show (Walk.cons f Q).toSubgraph.edgeSet ∪ A.toSubgraph.edgeSet ∪
        (R.reverse.append (Walk.cons h B)).toSubgraph.edgeSet =
        ((Walk.cons f Q).toSubgraph.edgeSet ∪
          (R.reverse.append (Walk.cons h B)).toSubgraph.edgeSet) ∪ A.toSubgraph.edgeSet by
      ext e; simp only [Set.mem_union]; tauto]
    rw [hcover]
    simp only [Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    ext e; simp only [Set.mem_union]; tauto
  · intro hwA
    have hwD : w ∈ (R.append (Walk.cons f B)).support :=
      (Walk.mem_support_append_iff _ _).mpr (Or.inl R.end_mem_support)
    exact hp.ne_of_mem_support_of_append hwu hwA hwD rfl

lemma maximum_cycle_first_visit_shortening {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i j : Fin k) (hij : i ≠ j) {a u v w b : V}
    (h : G.Adj u v) (Q : G.Walk v u) (hC : (Walk.cons h Q).IsCycle)
    (hi : (T.walk i).toSubgraph=(Walk.cons h Q).toSubgraph)
    (A : G.Walk a u) (R : G.Walk u w) (f : G.Adj w v) (B : G.Walk v b)
    (hp : (A.append (R.append (Walk.cons f B))).IsPath)
    (hA : ∀ x ∈ A.support, x ∈ (Walk.cons h Q).support → x=u)
    (hj : (T.walk j).toSubgraph=(A.append (R.append (Walk.cons f B))).toSubgraph) :
    ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U w,
      U.score=T.score ∧ M.cycle.length < (Walk.cons h Q).length := by
  classical
  have hd : Disjoint (Walk.cons h Q).toSubgraph.edgeSet
      (A.append (R.append (Walk.cons f B))).toSubgraph.edgeSet := by
    rw [←hi,←hj]; exact T.disjoint hij
  obtain ⟨hQA,hY,hX,hYX,hcover,hwu,hwA⟩ := cycle_first_visit_rotation h Q hC A R f B hp hA hd
  obtain ⟨U,hUi,_,_,hscore,hUa,hUb,_,_⟩ := replace_two_endpoints T i j hij w a w b
    (Walk.cons f (Q.append A.reverse)) (R.reverse.append (Walk.cons h B)) hY hX.isTrail hYX
    (by rw [hcover,←hi,←hj])
  rw [hi,hj,Walk.verts_toSubgraph,cycle_support_ncard hC,
    InducedBuffer.path_vertex_ncard _ hp,InducedBuffer.path_vertex_ncard _ hX] at hscore
  have hwQA : w ∈ (Q.append A.reverse).support := by
    by_contra hw
    have hYP : (Walk.cons f (Q.append A.reverse)).IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hQA,hw⟩
    rw [InducedBuffer.path_vertex_ncard _ hYP] at hscore
    have hb := hm U
    simp only [Walk.length_cons,Walk.length_append,Walk.length_reverse] at hscore
    omega
  have hvY : (Walk.cons f (Q.append A.reverse)).toSubgraph.verts=
      (Q.append A.reverse).toSubgraph.verts := by
    ext x
    simp only [Walk.mem_verts_toSubgraph,Walk.support_cons,List.mem_cons]
    exact or_iff_right_of_imp (fun hx ↦ hx ▸ hwQA)
  rw [hvY,InducedBuffer.path_vertex_ncard _ hQA] at hscore
  have hUs : U.score=T.score := by
    simp only [Walk.length_cons,Walk.length_append,Walk.length_reverse] at hscore
    omega
  have hwQ : w ∈ Q.support := by
    rcases (Walk.mem_support_append_iff Q A.reverse).mp hwQA with hw | hw
    · exact hw
    · exact (hwA (by simpa using hw)).elim
  obtain ⟨M,_,hMc,_⟩ := RootCycleMinimum.rep_of_cons U i hUa hUb f
    (Q.append A.reverse) hQA hY hUi hwQA
  have htake : ((Q.append A.reverse).takeUntil w hwQA).length=(Q.takeUntil w hwQ).length := by
    congr 1
    exact Walk.takeUntil_append_of_mem_left Q A.reverse hwQ
  have hlen := Walk.length_takeUntil_lt hwQ hwu
  refine ⟨U,M,hUs,?_⟩
  rw [hMc,htake,Walk.length_cons]
  omega

end Erdos583CycleFirstVisitRotationDevelopment
