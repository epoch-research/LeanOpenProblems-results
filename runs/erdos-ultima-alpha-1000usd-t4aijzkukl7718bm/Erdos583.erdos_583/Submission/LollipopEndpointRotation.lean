import Submission.CycleFirstVisitRotation

/-! Endpoint rotations retaining the old tail of a lollipop. -/
namespace Erdos583LollipopEndpointRotationDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583Work.LollipopEar Erdos583Work.TrailNormalization
open Erdos583CycleEndpointRotationDevelopment Erdos583GeneralPairEndpointsDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma lollipop_endpoint_rotation {V : Type*} {G : SimpleGraph V} {r v w b t : V}
    (h : G.Adj r v) (Q : G.Walk v r) (hC : (Walk.cons h Q).IsCycle)
    (S : G.Walk r t) (hS : S.IsPath)
    (hinter : ∀ x ∈ (Walk.cons h Q).support, x ∈ S.support → x=r)
    (A : G.Walk r w) (f : G.Adj w v) (B : G.Walk v b)
    (hp : (A.append (Walk.cons f B)).IsPath)
    (hd : Disjoint ((Walk.cons h Q).append S).toSubgraph.edgeSet
      (A.append (Walk.cons f B)).toSubgraph.edgeSet) :
    (Q.append S).IsPath ∧
      (Walk.cons f (Q.append S)).IsTrail ∧
      (A.reverse.append (Walk.cons h B)).IsPath ∧
      Disjoint (Walk.cons f (Q.append S)).toSubgraph.edgeSet
        (A.reverse.append (Walk.cons h B)).toSubgraph.edgeSet ∧
      (Walk.cons f (Q.append S)).toSubgraph.edgeSet ∪
          (A.reverse.append (Walk.cons h B)).toSubgraph.edgeSet=
        ((Walk.cons h Q).append S).toSubgraph.edgeSet ∪
          (A.append (Walk.cons f B)).toSubgraph.edgeSet ∧
      (A.reverse.append (Walk.cons h B)).toSubgraph.verts=
        (A.append (Walk.cons f B)).toSubgraph.verts ∧
      (Walk.cons f (Q.append S)).toSubgraph.verts=
        insert w ((Walk.cons h Q).append S).toSubgraph.verts ∧ w ≠ r := by
  classical
  have hQ := (Walk.cons_isCycle_iff Q h).mp hC |>.1
  have hQS : (Q.append S).IsPath := path_append_of_support_intersection hQ hS
    (fun x hxQ hxS ↦ hinter x (List.mem_cons_of_mem _ hxQ) hxS)
  have hd' := hd
  rw [Walk.toSubgraph_append,Subgraph.edgeSet_sup] at hd'
  have hdCS := edge_disjoint_of_one_common_vertex (Walk.cons h Q) S hinter
  obtain ⟨hY,hX,hYX,hcover,hXv,hYv,hwr⟩ := cycle_endpoint_rotation h Q hC A f B hp
    (disjoint_sup_left.mp hd').1
  have hnewS : Disjoint ((Walk.cons f Q).toSubgraph.edgeSet ∪
      (A.reverse.append (Walk.cons h B)).toSubgraph.edgeSet) S.toSubgraph.edgeSet := by
    rw [hcover]
    exact disjoint_sup_left.mpr ⟨hdCS,(disjoint_sup_left.mp hd').2.symm⟩
  have hYS := (disjoint_sup_left.mp hnewS).1
  have hXS := (disjoint_sup_left.mp hnewS).2
  have hnew : (Walk.cons f (Q.append S)).IsTrail := by
    rw [←Walk.cons_append]
    exact trail_append_of_disjoint hY hS.isTrail hYS
  refine ⟨hQS,hnew,hX,?_,?_,hXv,?_,hwr⟩
  · rw [←Walk.cons_append,Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    exact disjoint_sup_left.mpr ⟨hYX,hXS.symm⟩
  · rw [←Walk.cons_append,Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    rw [show (Walk.cons f Q).toSubgraph.edgeSet ∪ S.toSubgraph.edgeSet ∪
        (A.reverse.append (Walk.cons h B)).toSubgraph.edgeSet =
        ((Walk.cons f Q).toSubgraph.edgeSet ∪
          (A.reverse.append (Walk.cons h B)).toSubgraph.edgeSet) ∪ S.toSubgraph.edgeSet by
      ext e; simp only [Set.mem_union]; tauto]
    rw [hcover]
    simp only [Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    ext e; simp only [Set.mem_union]; tauto
  · rw [←Walk.cons_append]
    simp only [Walk.toSubgraph_append,Subgraph.verts_sup]
    rw [hYv]
    ext x; simp only [Set.mem_union,Set.mem_insert_iff]; tauto

lemma minimum_lollipop_predecessor_on_tail {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r)
    (hmin : ∀ W : TrailFamily G k, ∀ s : V, ∀ M : RootedCycleRep W s,
      W.score=T.score → L.cycle.length ≤ M.cycle.length)
    (j : Fin k) (hij : L.index ≠ j) {v w b : V}
    (h : G.Adj r v) (Q : G.Walk v r) (hC : L.cycle=Walk.cons h Q)
    (A : G.Walk r w) (f : G.Adj w v) (B : G.Walk v b)
    (hp : (A.append (Walk.cons f B)).IsPath)
    (hj : (T.walk j).toSubgraph=(A.append (Walk.cons f B)).toSubgraph) :
    w ∈ L.tail.support ∧ w ∉ L.cycle.support := by
  classical
  have hd : Disjoint ((Walk.cons h Q).append L.tail).toSubgraph.edgeSet
      (A.append (Walk.cons f B)).toSubgraph.edgeSet := by
    rw [←hC,←L.subgraph,←hj]; exact T.disjoint hij
  obtain ⟨hQS,hY,hX,hYX,hcover,hXv,hYv,hwr⟩ := lollipop_endpoint_rotation h Q (hC ▸ L.isCycle)
    L.tail L.isPath (hC ▸ L.inter) A f B hp hd
  obtain ⟨U,hUi,_,_,hscore,hUa,hUb,_,_⟩ := replace_two_endpoints T L.index j hij w L.finish w b
    (Walk.cons f (Q.append L.tail)) (A.reverse.append (Walk.cons h B)) hY hX.isTrail hYX
    (by rw [hcover,←hC,←L.subgraph,←hj])
  rw [L.subgraph,hC,hj,hXv,hYv] at hscore
  have hwL : w ∈ ((Walk.cons h Q).append L.tail).toSubgraph.verts := by
    by_contra hw
    rw [Set.ncard_insert_of_notMem hw] at hscore
    have hh := hm U
    omega
  rw [Set.insert_eq_of_mem hwL] at hscore
  have hUs : U.score=T.score := by omega
  have hwQS : w ∈ (Q.append L.tail).support := by
    rw [Walk.cons_append] at hwL
    exact (List.mem_cons.mp ((Walk.cons h (Q.append L.tail)).mem_verts_toSubgraph.mp hwL)).resolve_left hwr
  have hwC : w ∉ L.cycle.support := by
    intro hwC
    have hwQ : w ∈ Q.support := by
      rw [hC] at hwC
      exact (List.mem_cons.mp hwC).resolve_left hwr
    obtain ⟨M,_,hMc,_⟩ := RootCycleMinimum.rep_of_cons U L.index hUa hUb f
      (Q.append L.tail) hQS hY hUi hwQS
    have ht : ((Q.append L.tail).takeUntil w hwQS).length=(Q.takeUntil w hwQ).length := by
      congr 1
      exact Walk.takeUntil_append_of_mem_left Q L.tail hwQ
    have hl := Walk.length_takeUntil_lt hwQ hwr
    have hh := hmin U w M hUs
    rw [hMc,ht,hC,Walk.length_cons] at hh
    omega
  refine ⟨?_,hwC⟩
  rcases (Walk.mem_support_append_iff Q L.tail).mp hwQS with hwQ | hwS
  · exact (hwC (by rw [hC]; exact List.mem_cons_of_mem _ hwQ)).elim
  · exact hwS

lemma maximum_lollipop_shared_start_neighbor_present {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (j : Fin k) (hij : L.index ≠ j)
    {v b : V} (h : G.Adj r v) (Q : G.Walk v r) (hC : L.cycle=Walk.cons h Q)
    (P : G.Walk r b) (hp : P.IsPath) (hj : (T.walk j).toSubgraph=P.toSubgraph) :
    v ∈ P.support := by
  classical
  let R := Q.append L.tail
  have hQ := (Walk.cons_isCycle_iff Q h).mp (hC ▸ L.isCycle) |>.1
  have hR : R.IsPath := path_append_of_support_intersection hQ L.isPath
    (fun x hxQ hxS ↦ L.inter x (by rw [hC]; exact List.mem_cons_of_mem _ hxQ) hxS)
  have hL : (Walk.cons h R).IsTrail := by
    rw [show Walk.cons h R=L.cycle.append L.tail by rw [hC,Walk.cons_append]]
    exact trail_append_of_disjoint L.isCycle.isTrail L.isPath.isTrail
      (edge_disjoint_of_one_common_vertex _ _ L.inter)
  have hi : (T.walk L.index).toSubgraph=(Walk.cons h R).toSubgraph := by
    rw [L.subgraph,hC,Walk.cons_append]
  have hd : Disjoint (Walk.cons h R).toSubgraph.edgeSet P.toSubgraph.edgeSet := by
    rw [←hi,←hj]; exact T.disjoint hij
  obtain ⟨_,hX,hd',hcover⟩ := MobileDefect.same_root_transfer_data h R P hL hp.isTrail hd
  obtain ⟨U,_,_,_,hscore,_,_,_,_⟩ := replace_two_endpoints T L.index j hij v L.finish v b
    R (Walk.cons h.symm P) hR.isTrail hX hd' (by rw [hcover,←hi,←hj])
  have hrR : r ∈ R.support := (Walk.mem_support_append_iff Q L.tail).mpr (Or.inl Q.end_mem_support)
  rw [hi,cons_ncard_of_mem h R hrR,hj] at hscore
  by_contra hv
  rw [cons_ncard_of_notMem h.symm P hv] at hscore
  have hh := hm U
  omega

lemma minimum_lollipop_root_path_predecessor {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r)
    (hmin : ∀ W : TrailFamily G k, ∀ s : V, ∀ M : RootedCycleRep W s,
      W.score=T.score → L.cycle.length ≤ M.cycle.length)
    (j : Fin k) (hij : L.index ≠ j) {v b : V}
    (hv : L.cycle.toSubgraph.Adj r v)
    (P : G.Walk r b) (hp : P.IsPath) (hj : (T.walk j).toSubgraph=P.toSubgraph) :
    ∃ w, ∃ A : G.Walk r w, ∃ f : G.Adj w v, ∃ B : G.Walk v b,
      P=A.append (Walk.cons f B) ∧ w ∈ L.tail.support ∧ w ∉ L.cycle.support := by
  obtain ⟨Q,hQ,hQC⟩ := CycleFirstVisits.cycle_edge_first L.cycle L.isCycle
    (L.cycle.toSubgraph.adj_sub hv) (L.cycle.mem_edges_toSubgraph.mp hv)
  let N : RootedCycleRep T r :=
    ⟨L.index,L.finish,L.start_eq,L.finish_eq,Walk.cons (L.cycle.toSubgraph.adj_sub hv) Q,
      L.tail,hQ,L.isPath,(by
        intro x hx hxS
        exact L.inter x (L.cycle.mem_verts_toSubgraph.mp (hQC ▸
          (Walk.cons (L.cycle.toSubgraph.adj_sub hv) Q).mem_verts_toSubgraph.mpr hx)) hxS),
      by rw [Walk.toSubgraph_append,hQC,←Walk.toSubgraph_append]; exact L.subgraph⟩
  have hlen : N.cycle.length=L.cycle.length := by
    change (Walk.cons (L.cycle.toSubgraph.adj_sub hv) Q).length=L.cycle.length
    rw [←trail_edgeSet_ncard _ hQ.isTrail,hQC,trail_edgeSet_ncard _ L.isCycle.isTrail]
  have hminN : ∀ W : TrailFamily G k, ∀ s : V, ∀ M : RootedCycleRep W s,
      W.score=T.score → N.cycle.length ≤ M.cycle.length := by
    intro W s M hWs; rw [hlen]; exact hmin W s M hWs
  have hvP := maximum_lollipop_shared_start_neighbor_present T hm r N j hij
    (L.cycle.toSubgraph.adj_sub hv) Q rfl P hp hj
  obtain ⟨w,A,f,hA⟩ := TerminalTail.nonnil_last_edge (P.takeUntil v hvP)
    (Walk.not_nil_of_ne (L.cycle.toSubgraph.adj_sub hv).ne)
  let B := P.dropUntil v hvP
  have hform : P=A.append (Walk.cons f B) := by
    calc
      P=(P.takeUntil v hvP).append B := (Walk.take_spec P hvP).symm
      _=(A.concat f).append B := by rw [hA]
      _=A.append (Walk.cons f B) := by
        rw [Walk.concat_eq_append,←Walk.append_assoc,Walk.cons_nil_append]
  obtain ⟨hwS,hwC⟩ := minimum_lollipop_predecessor_on_tail T hm r N hminN j hij
    (L.cycle.toSubgraph.adj_sub hv) Q rfl A f B (hform ▸ hp) (hj.trans (congrArg Walk.toSubgraph hform))
  refine ⟨w,A,f,B,hform,hwS,?_⟩
  intro hw
  apply hwC
  change w ∈ (Walk.cons (L.cycle.toSubgraph.adj_sub hv) Q).support
  rw [←Walk.mem_verts_toSubgraph,hQC,Walk.mem_verts_toSubgraph]
  exact hw

end Erdos583LollipopEndpointRotationDevelopment
