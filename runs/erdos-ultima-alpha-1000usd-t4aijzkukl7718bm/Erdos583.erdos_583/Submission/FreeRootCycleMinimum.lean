import Submission.CycleEndpointRotation
import Submission.GeneralPairEndpoints

/-! Shortest rooted cycles with unrestricted root and endpoint quotas.
Unlike the energy-constrained minimum, this minimum compares every family
of the same score, even when the quota energy changes. -/
namespace Erdos583FreeRootCycleMinimumDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583Work.LollipopEar
open Erdos583CycleEndpointRotationDevelopment Erdos583GeneralPairEndpointsDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma exists_unrestricted_shortest_cycle {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (hs : T.score+1=G.edgeSet.ncard+k) (hr : HasRoot T r) :
    ∃ U : TrailFamily G k, ∃ s : V, ∃ L : RootedCycleRep U s,
      U.score=T.score ∧
      ∀ W : TrailFamily G k, ∀ t : V, ∀ M : RootedCycleRep W t,
        W.score=U.score → L.cycle.length ≤ M.cycle.length := by
  classical
  obtain ⟨R,hRs,_,_,⟨N⟩⟩ := exists_rooted_cycle_rep T r hs hr
  let P (n : ℕ) := ∃ U : TrailFamily G k, ∃ s : V, ∃ L : RootedCycleRep U s,
    U.score=T.score ∧ L.cycle.length=n
  have hex : ∃ n, P n := ⟨N.cycle.length,R,r,N,hRs,rfl⟩
  obtain ⟨U,s,L,hUs,hL⟩ := Nat.find_spec hex
  refine ⟨U,s,L,hUs,?_⟩
  intro W t M hWs
  rw [hL]
  exact Nat.find_min' hex ⟨W,t,M,hWs.trans hUs,rfl⟩

lemma maximum_cycle_endpoint_shortening {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i j : Fin k) (hij : i ≠ j) {u v w b : V}
    (h : G.Adj u v) (Q : G.Walk v u) (hC : (Walk.cons h Q).IsCycle)
    (hi : (T.walk i).toSubgraph=(Walk.cons h Q).toSubgraph)
    (A : G.Walk u w) (f : G.Adj w v) (B : G.Walk v b)
    (hp : (A.append (Walk.cons f B)).IsPath)
    (hj : (T.walk j).toSubgraph=(A.append (Walk.cons f B)).toSubgraph) :
    ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U w,
      U.score=T.score ∧ M.cycle.length < (Walk.cons h Q).length := by
  classical
  have hd : Disjoint (Walk.cons h Q).toSubgraph.edgeSet
      (A.append (Walk.cons f B)).toSubgraph.edgeSet := by rw [←hi,←hj]; exact T.disjoint hij
  obtain ⟨hY,hX,hYX,hcover,hXv,hYv,hwu⟩ := cycle_endpoint_rotation h Q hC A f B hp hd
  obtain ⟨U,hUi,_,_,hscore,hUa,hUb,_,_⟩ := replace_two_endpoints T i j hij w u w b
    (Walk.cons f Q) (A.reverse.append (Walk.cons h B)) hY hX.isTrail hYX
    (by rw [hcover,←hi,←hj])
  rw [hi,hj,hXv,hYv] at hscore
  have hwC : w ∈ (Walk.cons h Q).toSubgraph.verts := by
    by_contra hw
    rw [Set.ncard_insert_of_notMem hw] at hscore
    have hb := hm U
    omega
  rw [Set.insert_eq_of_mem hwC] at hscore
  have hUs : U.score=T.score := by omega
  have hwQ : w ∈ Q.support := by
    have hw := (Walk.cons h Q).mem_verts_toSubgraph.mp hwC
    exact (List.mem_cons.mp hw).resolve_left hwu
  have hQ := (Walk.cons_isCycle_iff Q h).mp hC |>.1
  obtain ⟨M,_,hMc,_⟩ := RootCycleMinimum.rep_of_cons U i hUa hUb f Q hQ hY hUi hwQ
  have hlen := Walk.length_takeUntil_lt hwQ hwu
  exact ⟨U,M,hUs,by rw [hMc,Walk.length_cons]; omega⟩

lemma minimum_whole_cycle_path_start_avoids {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i j : Fin k) (hij : i ≠ j) {r u b : V}
    (C : G.Walk r r) (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hmin : ∀ W : TrailFamily G k, ∀ t : V, ∀ M : RootedCycleRep W t,
      W.score=T.score → C.length ≤ M.cycle.length)
    (P : G.Walk u b) (hp : P.IsPath) (hj : (T.walk j).toSubgraph=P.toSubgraph) :
    u ∉ C.support := by
  classical
  intro hu
  let D := C.rotate hu
  have hD : D.IsCycle := hC.rotate hu
  have hDC : D.toSubgraph=C.toSubgraph := C.toSubgraph_rotate hu
  obtain ⟨v,h,Q,hcycle,hsub⟩ : ∃ v, ∃ h : G.Adj u v, ∃ Q : G.Walk v u,
      (Walk.cons h Q).IsCycle ∧ (Walk.cons h Q).toSubgraph=C.toSubgraph := by
    cases hd : D with
    | nil => exact (hD.not_nil (hd ▸ Walk.Nil.nil)).elim
    | cons h Q => exact ⟨_,h,Q,hd ▸ hD,hd ▸ hDC⟩
  have hi' : (T.walk i).toSubgraph=(Walk.cons h Q).toSubgraph := hi.trans hsub.symm
  have hpj : (T.walk j).IsPath := ProtectedEdge.trail_isPath_of_subgraph_eq
    (T.walk j) P (T.isTrail j) hp hj
  have hvP : v ∈ P.support := by
    by_contra hvP
    apply PentagonIntersection.maximal_cycle_not_absorbable T hm i j hij (Walk.cons h Q) hcycle hi' hpj
    have hd : Disjoint (Walk.nil.append P).toSubgraph.edgeSet (Walk.cons h Q).toSubgraph.edgeSet := by
      simp only [Walk.nil_append]
      rw [←hj,←hi']
      exact T.disjoint hij.symm
    have hcover := CycleFirstVisits.cycle_missing_first_neighbor (Walk.cons h Q) hcycle
      (.nil : G.Walk u u) P (by simpa only [Walk.nil_append] using hp)
      (fun z hz _ ↦ by simpa only [Walk.support_nil,List.mem_singleton] using hz)
      (show (Walk.cons h Q).toSubgraph.Adj u v from by
        simpa only [Walk.snd_cons] using (Walk.cons h Q).toSubgraph_adj_snd (by simp)) hvP hd
    simpa only [Walk.nil_append,←hj,Set.union_comm] using hcover
  obtain ⟨w,A,f,hA⟩ := TerminalTail.nonnil_last_edge (P.takeUntil v hvP)
    (Walk.not_nil_of_ne h.ne)
  let B := P.dropUntil v hvP
  have hform : P=A.append (Walk.cons f B) := by
    calc
      P=(P.takeUntil v hvP).append B := (Walk.take_spec P hvP).symm
      _=(A.concat f).append B := by rw [hA]
      _=A.append (Walk.cons f B) := by rw [Walk.concat_eq_append,←Walk.append_assoc,Walk.cons_nil_append]
  obtain ⟨U,M,hUs,hshort⟩ := maximum_cycle_endpoint_shortening T hm i j hij h Q hcycle hi'
    A f B (hform ▸ hp) (hj.trans (congrArg Walk.toSubgraph hform))
  have hlen : (Walk.cons h Q).length=C.length := by
    rw [←trail_edgeSet_ncard _ hcycle.isTrail,hsub,trail_edgeSet_ncard C hC.isTrail]
  have hh := hmin U w M hUs
  omega

lemma minimum_whole_cycle_other_endpoints_avoid {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i : Fin k) {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hmin : ∀ W : TrailFamily G k, ∀ t : V, ∀ M : RootedCycleRep W t,
      W.score=T.score → C.length ≤ M.cycle.length)
    (hp : ∀ j, j ≠ i → (T.walk j).IsPath) :
    ∀ j, j ≠ i → T.start j ∉ C.support ∧ T.finish j ∉ C.support := by
  intro j hji
  constructor
  · exact minimum_whole_cycle_path_start_avoids T hm i j hji.symm C hC hi hmin
      (T.walk j) (hp j hji) rfl
  · exact minimum_whole_cycle_path_start_avoids T hm i j hji.symm C hC hi hmin
      (T.walk j).reverse (hp j hji).reverse (Walk.toSubgraph_reverse _).symm

end Erdos583FreeRootCycleMinimumDevelopment
