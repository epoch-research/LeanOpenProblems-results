import Submission.TriangleFreshTail

/-! An arbitrary-length cycle ear can be exchanged with a chord in a path
which avoids its internal vertices. The attached tail and endpoint quotas
are retained. -/
namespace Erdos583LongLollipopEarDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583Work.LollipopEar
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma path_expand_fresh_path {a b u v : V} (P : G.Walk a b) (hp : P.IsPath)
    (A : G.Walk u v) (hA : A.IsPath) (he : s(u,v) ∈ P.edges)
    (hfresh : ∀ z ∈ A.support, z ≠ u → z ≠ v → z ∉ P.support) :
    ∃ Q : G.Walk a b, Q.IsPath ∧
      Q.toSubgraph.edgeSet=(P.toSubgraph.edgeSet \ {s(u,v)}) ∪ A.toSubgraph.edgeSet := by
  let H := P.toSubgraph.spanningCoe
  have hedge : ∀ e ∈ P.edges, e ∈ H.edgeSet := fun _ hh ↦ P.mem_edges_toSubgraph.mpr hh
  let P' := P.transfer H hedge
  have hf : ∀ z ∈ A.support, z ≠ u → z ≠ v → z ∉ H.support := by
    intro z hz hzu hzv ⟨y,hy⟩
    exact hfresh z hz hzu hzv (Walk.mem_support_of_adj_toSubgraph (show P.toSubgraph.Adj z y from hy))
  obtain ⟨Q,hQ,hQe⟩ := path_expand_edge A hA
    ((H.deleteEdges_le _).trans P.toSubgraph.spanningCoe_le) hf P' (hp.transfer hedge)
  exact ⟨Q,hQ,by simpa only [P',Walk.edgeSet_toSubgraph,Walk.edges_transfer,he,if_true] using hQe⟩

lemma long_cycle_ear_exchange {a b u v : V} (A : G.Walk u v) (B : G.Walk v u)
    (hC : (A.append B).IsCycle) (h : G.Adj u v)
    (P : G.Walk a b) (hp : P.IsPath) (he : s(u,v) ∈ P.edges)
    (hfresh : ∀ z ∈ A.support, z ≠ u → z ≠ v → z ∉ P.support)
    (hd : Disjoint (A.append B).toSubgraph.edgeSet P.toSubgraph.edgeSet) :
    (Walk.cons h B).IsCycle ∧ ∃ Q : G.Walk a b, Q.IsPath ∧
      Disjoint (Walk.cons h B).toSubgraph.edgeSet Q.toSubgraph.edgeSet ∧
      (Walk.cons h B).toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet=
        (A.append B).toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet ∧
      (Walk.cons h B).length+A.length=(A.append B).length+1 := by
  have hA := hC.isPath_of_append_left (Walk.not_nil_of_ne h.ne.symm)
  have hB := hC.isPath_of_append_right (Walk.not_nil_of_ne h.ne)
  have hdAP : Disjoint A.toSubgraph.edgeSet P.toSubgraph.edgeSet := by
    rw [Walk.toSubgraph_append,Subgraph.edgeSet_sup] at hd
    exact (disjoint_sup_left.mp hd).1
  have hdBP : Disjoint B.toSubgraph.edgeSet P.toSubgraph.edgeSet := by
    rw [Walk.toSubgraph_append,Subgraph.edgeSet_sup] at hd
    exact (disjoint_sup_left.mp hd).2
  have hdAB := RootedTailSystem.append_trail_disjoint hC.isTrail
  have heA : s(u,v) ∉ A.toSubgraph.edgeSet := fun hh ↦
    Set.disjoint_left.mp hdAP hh (P.mem_edges_toSubgraph.mpr he)
  have heB : s(u,v) ∉ B.edges := fun hh ↦
    Set.disjoint_left.mp hdBP (B.mem_edges_toSubgraph.mpr hh) (P.mem_edges_toSubgraph.mpr he)
  have hnew := (Walk.cons_isCycle_iff B h).mpr ⟨hB,heB⟩
  obtain ⟨Q,hQ,hQe⟩ := path_expand_fresh_path P hp A hA he hfresh
  have hDe : (Walk.cons h B).toSubgraph.edgeSet={s(u,v)} ∪ B.toSubgraph.edgeSet := by
    ext e
    simp
  refine ⟨hnew,Q,hQ,?_,?_,by simp only [Walk.length_cons,Walk.length_append]; omega⟩
  · rw [hDe,hQe]
    apply Set.disjoint_left.mpr
    intro e heD heQ
    rcases heD with heD | heD <;> rcases heQ with heQ | heQ
    · exact heQ.2 heD
    · exact heA ((Set.mem_singleton_iff.mp heD) ▸ heQ)
    · exact Set.disjoint_left.mp hdBP heD heQ.1
    · exact Set.disjoint_left.mp hdAB heQ heD
  · rw [hDe,hQe,Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    ext e
    simp only [Set.mem_union,Set.mem_diff,Set.mem_singleton_iff]
    by_cases hh : e=s(u,v)
    · subst e
      simp [he]
    · tauto

lemma long_ear_exchange_with_tail {a b d u v r : V}
    (A : G.Walk u v) (B : G.Walk v u) (hc : (A.append B).IsCycle) (hr : r ∈ B.support)
    (S : G.Walk r b) (hS : S.IsPath)
    (hinter : ∀ z ∈ (A.append B).support, z ∈ S.support → z=r)
    (P : G.Walk a d) (hp : P.IsPath) (h : G.Adj u v) (he : s(u,v) ∈ P.edges)
    (hfresh : ∀ z ∈ A.support, z ≠ u → z ≠ v → z ∉ P.support)
    (hd : Disjoint ((A.append B).toSubgraph.edgeSet ∪ S.toSubgraph.edgeSet) P.toSubgraph.edgeSet) :
    ∃ E : G.Walk r r, ∃ Q : G.Walk a d,
      E.IsCycle ∧ Q.IsPath ∧ E.length+A.length=(A.append B).length+1 ∧
      E.toSubgraph.verts ⊆ (A.append B).toSubgraph.verts ∧
      (∀ z ∈ E.support, z ∈ S.support → z=r) ∧ (E.append S).IsTrail ∧
      Disjoint (E.append S).toSubgraph.edgeSet Q.toSubgraph.edgeSet ∧
      (E.append S).toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet=
        ((A.append B).toSubgraph.edgeSet ∪ S.toSubgraph.edgeSet) ∪ P.toSubgraph.edgeSet := by
  obtain ⟨hD,Q,hQ,hsep,hcover,hlen⟩ := long_cycle_ear_exchange A B hc h P hp he hfresh
    (disjoint_sup_left.mp hd).1
  let D := Walk.cons h B
  have hrD : r ∈ D.support := List.mem_cons_of_mem _ hr
  let E := D.rotate hrD
  have hE := hD.rotate hrD
  have hED : E.toSubgraph=D.toSubgraph := D.toSubgraph_rotate hrD
  have hElen : E.length=D.length := by
    rw [←trail_edgeSet_ncard E hE.isTrail,hED,trail_edgeSet_ncard D hD.isTrail]
  have hsub : E.toSubgraph.verts ⊆ (A.append B).toSubgraph.verts := by
    intro z hz
    rw [hED,Walk.mem_verts_toSubgraph] at hz
    have hzB : z ∈ B.support := by
      rcases (List.mem_cons.mp hz) with rfl|hzB
      · exact B.end_mem_support
      · exact hzB
    rw [Walk.mem_verts_toSubgraph,Walk.mem_support_append_iff]
    exact Or.inr hzB
  have hint : ∀ z ∈ E.support, z ∈ S.support → z=r := by
    intro z hzE hzS
    exact hinter z ((A.append B).mem_verts_toSubgraph.mp (hsub (E.mem_verts_toSubgraph.mpr hzE))) hzS
  have hES := edge_disjoint_of_one_common_vertex E S hint
  have hCS := edge_disjoint_of_one_common_vertex (A.append B) S hinter
  have hQS : Disjoint Q.toSubgraph.edgeSet S.toSubgraph.edgeSet := by
    apply (disjoint_sup_left.mpr ⟨hCS,(disjoint_sup_left.mp hd).2.symm⟩).mono_left
    intro e heQ
    change e ∈ (A.append B).toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet
    rw [←hcover]
    exact Or.inr heQ
  have hEQ : Disjoint E.toSubgraph.edgeSet Q.toSubgraph.edgeSet := by rw [hED]; exact hsep
  have hsep' : Disjoint (E.append S).toSubgraph.edgeSet Q.toSubgraph.edgeSet := by
    rw [Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    exact disjoint_sup_left.mpr ⟨hEQ,hQS.symm⟩
  have hcover' : (E.append S).toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet=
      ((A.append B).toSubgraph.edgeSet ∪ S.toSubgraph.edgeSet) ∪ P.toSubgraph.edgeSet := by
    rw [Walk.toSubgraph_append,Subgraph.edgeSet_sup,hED]
    have hh : D.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet=(A.append B).toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet := hcover
    calc
      _ = (D.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet) ∪ S.toSubgraph.edgeSet := by ac_rfl
      _ = _ := by rw [hh]; ac_rfl
  exact ⟨E,Q,hE,hQ,by rw [hElen]; exact hlen,hsub,hint,
    trail_append_of_disjoint hE.isTrail hS.isTrail hES,hsep',hcover'⟩

lemma shorten_rooted_member_long_ear {k : ℕ} (T : TrailFamily G k) (i j : Fin k) (hij : i ≠ j)
    (C : G.Walk (T.start i) (T.start i)) (hc : C.IsCycle)
    (S : G.Walk (T.start i) (T.finish i)) (hS : S.IsPath)
    (hinter : ∀ z ∈ C.support, z ∈ S.support → z=T.start i)
    (hi : (T.walk i).toSubgraph=(C.append S).toSubgraph)
    {u v : V} (A : G.Walk u v) (B : G.Walk v u)
    (hD : (A.append B).IsCycle) (hDC : (A.append B).toSubgraph=C.toSubgraph)
    (hr : T.start i ∈ B.support)
    (hj : (T.walk j).IsPath) (huv : G.Adj u v)
    (he : s(u,v) ∈ (T.walk j).edges)
    (hfresh : ∀ z ∈ A.support, z ≠ u → z ≠ v → z ∉ (T.walk j).support) :
    ∃ U : TrailFamily G k, ∃ E : G.Walk (T.start i) (T.start i),
      U.score=T.score ∧ (∀ z, U.quota z=T.quota z) ∧ HasRoot U (T.start i) ∧
      U.start i=T.start i ∧ U.finish i=T.finish i ∧ E.IsCycle ∧ E.length+A.length=C.length+1 ∧
      (U.walk i).toSubgraph=(E.append S).toSubgraph ∧
      (∀ z ∈ E.support, z ∈ S.support → z=T.start i) := by
  classical
  have hd : Disjoint ((A.append B).toSubgraph.edgeSet ∪ S.toSubgraph.edgeSet)
      (T.walk j).toSubgraph.edgeSet := by
    rw [hDC,←Subgraph.edgeSet_sup,←Walk.toSubgraph_append,←hi]
    exact T.disjoint hij
  have hintD (z : V) (hzD : z ∈ (A.append B).support)
      (hzS : z ∈ S.support) : z=T.start i := by
    apply hinter z _ hzS
    rwa [←Walk.mem_verts_toSubgraph,hDC,Walk.mem_verts_toSubgraph] at hzD
  obtain ⟨E,Q,hE,hQ,hlen,hsub,hint,htrail,hsep,hcover⟩ :=
    long_ear_exchange_with_tail A B hD hr S hS hintD (T.walk j) hj huv he hfresh hd
  have hcover' : (E.append S).toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet =
      (T.walk i).toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet := by
    rw [hcover,hDC,←Subgraph.edgeSet_sup,←Walk.toSubgraph_append,←hi]
  obtain ⟨U,hUi,hUj,hparts,hstarts,hfinish,hscore,hquota⟩ :=
    replace_two_starts_general T i j hij (T.start i) (T.start j) (E.append S) Q
      htrail hQ.isTrail hsep hcover'
  have hUa : U.start i=T.start i := by rw [hstarts]; simp
  have hUb : U.finish i=T.finish i := congrFun hfinish i
  have hUroot : HasRoot U (T.start i) := ThreeTransfer.hasRoot_of_append_rep U i hUa hUb
    E S hE.not_nil htrail S.start_mem_support hUi
  have hDl : (A.append B).length=C.length := by
    rw [←trail_edgeSet_ncard _ hD.isTrail,hDC,trail_edgeSet_ncard C hc.isTrail]
  have hCS := edge_disjoint_of_one_common_vertex C S hinter
  have hCStrail := trail_append_of_disjoint hc.isTrail hS.isTrail hCS
  have hlenold : (T.walk i).length=(C.append S).length := by
    rw [←trail_edgeSet_ncard _ (T.isTrail i),hi,trail_edgeSet_ncard _ hCStrail]
  have hsumlen := congrArg Set.ncard hcover'
  rw [Set.ncard_union_eq hsep,Set.ncard_union_eq (T.disjoint hij),
    trail_edgeSet_ncard _ htrail,trail_edgeSet_ncard _ hQ.isTrail,
    trail_edgeSet_ncard _ (T.isTrail i),trail_edgeSet_ncard _ hj.isTrail,hlenold] at hsumlen
  rw [hi,lollipop_vertex_card C hc S hS hinter,lollipop_vertex_card E hE S hS hint,
    (walk_vertex_ncard_eq_iff _).mpr hj,(walk_vertex_ncard_eq_iff _).mpr hQ] at hscore
  refine ⟨U,E,by omega,?_,hUroot,hUa,hUb,hE,hlen.trans (congrArg (fun q : ℕ ↦ q+1) hDl),hUi,hint⟩
  intro z
  have hh := hquota z
  omega


lemma no_long_cycle_ear {k : ℕ} (T : TrailFamily G k) (r : V) (L : RootedCycleRep T r)
    (hmin : ∀ W : TrailFamily G k, ∀ M : RootedCycleRep W r,
      W.score=T.score → (∀ z, W.quota z=T.quota z) → L.cycle.length ≤ M.cycle.length)
    (j : Fin k) (hij : L.index ≠ j) {u v : V}
    (A : G.Walk u v) (B : G.Walk v u) (hC : (A.append B).IsCycle)
    (hCE : (A.append B).toSubgraph=L.cycle.toSubgraph) (hr : r ∈ B.support)
    (hA : 2 ≤ A.length) (hj : (T.walk j).IsPath) (h : G.Adj u v)
    (he : s(u,v) ∈ (T.walk j).edges)
    (hfresh : ∀ z ∈ A.support, z ≠ u → z ≠ v → z ∉ (T.walk j).support) : False := by
  rcases L with ⟨i,b,ha,hb,C,S,hCy,hS,hinter,hsub⟩
  dsimp only at *
  subst r b
  obtain ⟨U,E,hUs,hUq,_,hUa,hUb,hE,hEl,hUi,hint⟩ :=
    shorten_rooted_member_long_ear T i j hij C hCy S hS hinter hsub A B hC hCE hr hj h he hfresh
  let M : RootedCycleRep U (T.start i) := ⟨i,T.finish i,hUa,hUb,E,S,hE,hS,hint,hUi⟩
  have hh := hmin U M hUs hUq
  change C.length ≤ E.length at hh
  omega

end Erdos583LongLollipopEarDevelopment
