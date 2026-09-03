import Submission.Work

/-! Shortening a private two-edge ear in the tail of a rooted defect. The
cycle is retained literally, and every endpoint quota is preserved. -/
namespace Erdos583TailEarDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.QuotaRooted
open scoped Classical
set_option maxHeartbeats 1600000

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
lemma shortcut_support_subset {r b u v w : V} (A : G.Walk r u) (B : G.Walk w b)
    (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w) :
    (A.append (Walk.cons huw B)).support ⊆ (A.append (Walk.cons huv (Walk.cons hvw B))).support := by
  intro x hx
  simp only [Walk.mem_support_append_iff,Walk.support_cons,List.mem_cons] at hx ⊢
  tauto

omit [Fintype V] in
lemma shortcut_isPath {r b u v w : V} (A : G.Walk r u) (B : G.Walk w b)
    (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w)
    (hp : (A.append (Walk.cons huv (Walk.cons hvw B))).IsPath) :
    (A.append (Walk.cons huw B)).IsPath := by
  induction A with
  | nil =>
    simp only [Walk.nil_append,Walk.cons_isPath_iff,Walk.support_cons,List.mem_cons,not_or] at hp ⊢
    exact ⟨hp.1.1,hp.2.2⟩
  | cons h A ih =>
    rw [Walk.cons_append,Walk.cons_isPath_iff] at hp ⊢
    exact ⟨ih huv huw hp.1,fun hx ↦ hp.2 (shortcut_support_subset A B huv hvw huw hx)⟩

omit [Fintype V] in
lemma shortcut_avoids_ear {r b u v w : V} (A : G.Walk r u) (B : G.Walk w b)
    (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w)
    (hp : (A.append (Walk.cons huv (Walk.cons hvw B))).IsPath) :
    v ∉ (A.append (Walk.cons huw B)).support := by
  have hA : v ∉ A.support := by
    intro hv
    exact (hp.ne_of_mem_support_of_append huv.ne.symm hv (by simp)) rfl
  have hB : v ∉ B.support := (Walk.cons_isPath_iff hvw B).mp
    ((Walk.cons_isPath_iff huv _).mp hp.of_append_right).1 |>.2
  simpa only [Walk.mem_support_append_iff,Walk.support_cons,List.mem_cons,not_or] using
    (show v ∉ A.support ∧ v ≠ u ∧ v ∉ B.support from ⟨hA,huv.ne.symm,hB⟩)

lemma tail_ear_exchange {r b a d u v w : V}
    (C : G.Walk r r) (_hc : C.IsCycle) (A : G.Walk r u) (B : G.Walk w b)
    (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w)
    (hp : (A.append (Walk.cons huv (Walk.cons hvw B))).IsPath)
    (hinter : ∀ z ∈ C.support, z ∈ (A.append (Walk.cons huv (Walk.cons hvw B))).support → z=r)
    (P : G.Walk a d) (hP : P.IsPath) (he : s(u,w) ∈ P.edges) (hvP : v ∉ P.support)
    (hd : Disjoint (C.append (A.append (Walk.cons huv (Walk.cons hvw B)))).toSubgraph.edgeSet P.toSubgraph.edgeSet) :
    ∃ Q : G.Walk a d, Q.IsPath ∧
      Disjoint (C.append (A.append (Walk.cons huw B))).toSubgraph.edgeSet Q.toSubgraph.edgeSet ∧
      (C.append (A.append (Walk.cons huw B))).toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet=
        (C.append (A.append (Walk.cons huv (Walk.cons hvw B)))).toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet := by
  classical
  let S := A.append (Walk.cons huv (Walk.cons hvw B))
  let R := A.append (Walk.cons huw B)
  have hRv : v ∉ R.support := shortcut_avoids_ear A B huv hvw huw hp
  have hvn : v ≠ r := fun h ↦ hRv (h ▸ R.start_mem_support)
  have hCv : v ∉ C.support := by
    intro hv
    apply hvn
    exact hinter v hv (by simp)
  have hnewv : v ∉ (C.append R).support := by
    simp only [Walk.mem_support_append_iff,not_or]
    exact ⟨hCv,hRv⟩
  obtain ⟨Q,hQ,hQe⟩ := CycleEar.path_expand_fresh_ear P hP huv hvw huw.ne he hvP
  let E := C.toSubgraph.edgeSet ∪ A.toSubgraph.edgeSet ∪ B.toSubgraph.edgeSet
  let F : Set (Sym2 V) := {s(u,v),s(v,w)}
  have hOld : (C.append S).toSubgraph.edgeSet=E ∪ F := by
    ext e
    simp only [S,E,F,Walk.mem_edges_toSubgraph,Walk.edges_append,Walk.edges_cons,List.mem_append,
      List.mem_cons,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff]
    tauto
  have hNew : (C.append R).toSubgraph.edgeSet=E ∪ {s(u,w)} := by
    ext e
    simp only [R,E,Walk.mem_edges_toSubgraph,Walk.edges_append,Walk.edges_cons,List.mem_append,
      List.mem_cons,Set.mem_union,Set.mem_singleton_iff]
    tauto
  have hsep : Disjoint (C.append R).toSubgraph.edgeSet Q.toSubgraph.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heN heQ
    rw [hQe] at heQ
    rcases heQ with heQ|heF
    · rw [hNew] at heN
      rcases heN with heE|heuw
      · exact Set.disjoint_left.mp hd (hOld.symm ▸ Or.inl heE) heQ.1
      · exact heQ.2 heuw
    · have hev : e ∈ ({s(u,v),s(v,w)} : Set (Sym2 V)) := heF
      rcases hev with heuv|hevw
      · have heuv : e=s(u,v) := heuv
        rw [heuv] at heN
        exact hnewv (Walk.mem_support_of_adj_toSubgraph heN.symm)
      · have hevw : e=s(v,w) := hevw
        rw [hevw] at heN
        exact hnewv (Walk.mem_support_of_adj_toSubgraph heN)
  refine ⟨Q,hQ,hsep,?_⟩
  rw [hNew,hOld,hQe]
  have heP : s(u,w) ∈ P.toSubgraph.edgeSet := P.mem_edges_toSubgraph.mpr he
  ext e
  simp only [F,Set.mem_union,Set.mem_diff,Set.mem_insert_iff,Set.mem_singleton_iff]
  by_cases heq : e=s(u,w)
  · subst e
    simp only [heP,eq_self,or_true,true_or]
  · tauto

lemma shorten_tail_at_fresh_ear {k : ℕ} (T : TrailFamily G k) (r : V)
    (L : LollipopEar.RootedCycleRep T r) (hs : T.score+1=G.edgeSet.ncard+k)
    (j : Fin k) (hij : L.index ≠ j) {u v w : V}
    (A : G.Walk r u) (B : G.Walk w L.finish)
    (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w)
    (hform : L.tail=A.append (Walk.cons huv (Walk.cons hvw B)))
    (he : s(u,w) ∈ (T.walk j).edges) (hvj : v ∉ (T.walk j).support) :
    ∃ U : TrailFamily G k, ∃ M : LollipopEar.RootedCycleRep U r,
      U.score=T.score ∧ (∀ x, U.quota x=T.quota x) ∧ M.cycle=L.cycle ∧
      M.tail.length+1=L.tail.length := by
  classical
  let R := A.append (Walk.cons huw B)
  have hp : (A.append (Walk.cons huv (Walk.cons hvw B))).IsPath := hform ▸ L.isPath
  have hR : R.IsPath := shortcut_isPath A B huv hvw huw hp
  have hint (z : V) (hz : z ∈ L.cycle.support) (hzR : z ∈ R.support) : z=r := by
    apply L.inter z hz
    rw [hform]
    exact shortcut_support_subset A B huv hvw huw hzR
  have hRtrail := trail_append_of_disjoint L.isCycle.isTrail hR.isTrail
    (LollipopEar.edge_disjoint_of_one_common_vertex L.cycle R hint)
  have hP := (T.one_defect_other_paths hs L.index L.member_not_path).2 j hij.symm
  have hd : Disjoint (L.cycle.append (A.append (Walk.cons huv (Walk.cons hvw B)))).toSubgraph.edgeSet
      (T.walk j).toSubgraph.edgeSet := by
    rw [←hform,←L.subgraph]
    exact T.disjoint hij
  obtain ⟨Q,hQ,hsep,hcover⟩ := tail_ear_exchange L.cycle L.isCycle A B huv hvw huw hp
    (by intro z hz hzS; exact L.inter z hz (hform.symm ▸ hzS)) (T.walk j) hP he hvj hd
  let W := (L.cycle.append R).copy rfl L.finish_eq.symm
  have hW : W.IsTrail := by simpa only [W,Walk.isTrail_copy] using hRtrail
  have hWe : W.toSubgraph=(L.cycle.append R).toSubgraph := NormalTrailSystem.walk_copy_subgraph _ _ _
  have hsep' : Disjoint W.toSubgraph.edgeSet Q.toSubgraph.edgeSet := by rw [hWe]; exact hsep
  have hcover' : W.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet=
      (T.walk L.index).toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet := by
    rw [hWe,hcover,←hform,←L.subgraph]
  obtain ⟨U,hUi,_,_,hstarts,hfinish,hscore,hquota⟩ := replace_two_starts_general T L.index j hij
    r (T.start j) W Q hW hQ.isTrail hsep' hcover'
  have hUa : U.start L.index=r := by rw [hstarts]; simp
  have hUb : U.finish L.index=L.finish := (congrFun hfinish L.index).trans L.finish_eq
  let M : LollipopEar.RootedCycleRep U r :=
    ⟨L.index,L.finish,hUa,hUb,L.cycle,R,L.isCycle,hR,hint,hUi.trans hWe⟩
  have hOldTrail := trail_append_of_disjoint L.isCycle.isTrail L.isPath.isTrail
    (LollipopEar.edge_disjoint_of_one_common_vertex L.cycle L.tail L.inter)
  have hOldLen : (T.walk L.index).length=(L.cycle.append L.tail).length := by
    rw [←trail_edgeSet_ncard _ (T.isTrail L.index),L.subgraph,trail_edgeSet_ncard _ hOldTrail]
  have hOldCard : (T.walk L.index).toSubgraph.verts.ncard=(T.walk L.index).length := by
    rw [L.subgraph,LollipopEar.lollipop_vertex_card L.cycle L.isCycle L.tail L.isPath L.inter,hOldLen]
  have hWCard : W.toSubgraph.verts.ncard=W.length := by
    rw [hWe,LollipopEar.lollipop_vertex_card L.cycle L.isCycle R hR hint]
    simp [W]
  have hsum := congrArg Set.ncard hcover'
  rw [Set.ncard_union_eq hsep',Set.ncard_union_eq (T.disjoint hij),
    trail_edgeSet_ncard W hW,trail_edgeSet_ncard Q hQ.isTrail,
    trail_edgeSet_ncard _ (T.isTrail L.index),trail_edgeSet_ncard _ (T.isTrail j)] at hsum
  rw [hOldCard,hWCard,(walk_vertex_ncard_eq_iff _).mpr hP,(walk_vertex_ncard_eq_iff _).mpr hQ] at hscore
  refine ⟨U,M,by omega,?_,rfl,?_⟩
  · intro x
    have hh := hquota x
    rw [L.start_eq] at hh
    omega
  · change R.length+1=L.tail.length
    rw [hform]
    simp [R]
    omega

omit [Fintype V] in
/-- A second optimization can retain the exact cycle, in addition to the
root, score and quota function, while minimizing the attached tail. -/
lemma exists_shortest_tail {k : ℕ} (T : TrailFamily G k) (r : V)
    (L : LollipopEar.RootedCycleRep T r) :
    ∃ U : TrailFamily G k, ∃ M : LollipopEar.RootedCycleRep U r,
      U.score=T.score ∧ (∀ x, U.quota x=T.quota x) ∧ M.cycle=L.cycle ∧
      ∀ W : TrailFamily G k, ∀ N : LollipopEar.RootedCycleRep W r,
        W.score=U.score → (∀ x, W.quota x=U.quota x) → N.cycle=M.cycle → M.tail.length ≤ N.tail.length := by
  classical
  let P (m : ℕ) := ∃ U : TrailFamily G k, ∃ M : LollipopEar.RootedCycleRep U r,
    U.score=T.score ∧ (∀ x, U.quota x=T.quota x) ∧ M.cycle=L.cycle ∧ M.tail.length=m
  have hex : ∃ m, P m := ⟨L.tail.length,T,L,rfl,fun _ ↦ rfl,rfl,rfl⟩
  obtain ⟨U,M,hUs,hUq,hC,hLen⟩ := Nat.find_spec hex
  refine ⟨U,M,hUs,hUq,hC,?_⟩
  intro W N hWs hWq hNC
  rw [hLen]
  exact Nat.find_min' hex ⟨W,N,hWs.trans hUs,fun x ↦ (hWq x).trans (hUq x),hNC.trans hC,rfl⟩

lemma shortest_tail_no_fresh_ear {k : ℕ} (T : TrailFamily G k) (r : V)
    (L : LollipopEar.RootedCycleRep T r) (hs : T.score+1=G.edgeSet.ncard+k)
    (hmin : ∀ U : TrailFamily G k, ∀ M : LollipopEar.RootedCycleRep U r,
      U.score=T.score → (∀ x, U.quota x=T.quota x) → M.cycle=L.cycle → L.tail.length ≤ M.tail.length)
    (j : Fin k) (hij : L.index ≠ j) {u v w : V}
    (A : G.Walk r u) (B : G.Walk w L.finish)
    (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w)
    (hform : L.tail=A.append (Walk.cons huv (Walk.cons hvw B)))
    (he : s(u,w) ∈ (T.walk j).edges) : v ∈ (T.walk j).support := by
  by_contra hvj
  obtain ⟨U,M,hUs,hUq,hC,hLen⟩ := shorten_tail_at_fresh_ear T r L hs j hij A B huv hvw huw hform he hvj
  have hh := hmin U M hUs hUq hC
  omega

omit [Fintype V] in
lemma internal_two_edge_form {r b v : V} (P : G.Walk r b) (hv : v ∈ P.support)
    (hvr : v ≠ r) (hvb : v ≠ b) :
    ∃ u w, ∃ A : G.Walk r u, ∃ B : G.Walk w b, ∃ huv : G.Adj u v, ∃ hvw : G.Adj v w,
      P=A.append (Walk.cons huv (Walk.cons hvw B)) := by
  obtain ⟨L,R,hform⟩ := P.mem_support_iff_exists_append.mp hv
  cases L with
  | nil => exact (hvr rfl).elim
  | cons h L =>
    obtain ⟨u,A,huv,hL⟩ := Walk.exists_cons_eq_concat h L
    cases R with
    | nil => exact (hvb rfl).elim
    | cons hvw B =>
      exact ⟨u,_,A,B,huv,hvw,by rw [hform,hL,Walk.concat_append]⟩

lemma tail_ear_chord_not_mem {r b u v w : V} (A : G.Walk r u) (B : G.Walk w b)
    (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w)
    (hp : (A.append (Walk.cons huv (Walk.cons hvw B))).IsPath) :
    s(u,w) ∉ (A.append (Walk.cons huv (Walk.cons hvw B))).edges := by
  intro he
  let P := A.append (Walk.cons huv (Walk.cons hvw B))
  let J := P.toSubgraph.spanningCoe
  have hJu : J.Adj u v := by
    change s(u,v) ∈ P.toSubgraph.edgeSet
    simp [P]
  have hJv : J.Adj v w := by
    change s(v,w) ∈ P.toSubgraph.edgeSet
    simp [P]
  have hJw : J.Adj u w := P.mem_edges_toSubgraph.mpr he
  let S : J.Walk u w := .cons hJu (.cons hJv .nil)
  let R : J.Walk u w := .cons hJw .nil
  have hS : S.IsPath := by simp [S,Walk.cons_isPath_iff,huv.ne,hvw.ne,huw.ne]
  have hR : R.IsPath := by simp [R,Walk.cons_isPath_iff,huw.ne]
  have hEq := (MatchingTrim.path_spanningCoe_isAcyclic P hp).path_unique ⟨S,hS⟩ ⟨R,hR⟩
  have hlen := congrArg (fun p : J.Path u w ↦ p.val.length) hEq
  norm_num [S,R] at hlen

lemma private_nonendpoint_degree_two {k : ℕ} (T : TrailFamily G k) (r : V)
    (L : LollipopEar.RootedCycleRep T r) (hs : T.score+1=G.edgeSet.ncard+k)
    {v : V} (hv : v ∈ L.tail.support) (hvr : v ≠ r) (hvb : v ≠ L.finish)
    (hprivate : ∀ j, j ≠ L.index → v ∉ (T.walk j).support) :
    Nat.card (G.neighborSet v)=2 := by
  classical
  have hvi : v ∈ (T.walk L.index).support := by
    rw [←Walk.mem_verts_toSubgraph,L.subgraph,Walk.mem_verts_toSubgraph,Walk.mem_support_append_iff]
    exact Or.inr hv
  have hfilter : (Finset.univ.filter fun j ↦ v ∈ (T.walk j).support)={L.index} := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    exact ⟨fun h ↦ by by_contra hne; exact hprivate j hne h,fun h ↦ h ▸ hvi⟩
  have hquota : T.quota v=0 := by
    rw [quota_eq_sum_endpoints]
    apply Finset.sum_eq_zero
    intro j _
    have hsne : T.start j ≠ v := by
      by_cases hj : j=L.index
      · subst j; rw [L.start_eq]; exact hvr.symm
      · intro heq; exact hprivate j hj (heq ▸ (T.walk j).start_mem_support)
    have hfne : T.finish j ≠ v := by
      by_cases hj : j=L.index
      · subst j; rw [L.finish_eq]; exact hvb.symm
      · intro heq; exact hprivate j hj (heq ▸ (T.walk j).end_mem_support)
    simp [hsne,hfne]
  have hh := RootCapacity.rooted_incidence T r hs L.hasRoot v
  rw [hquota,hfilter,Finset.card_singleton,if_neg hvr.symm] at hh
  omega

lemma shortest_tail_internal_not_private {n k : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G k) (r : Fin n) (L : LollipopEar.RootedCycleRep T r)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hmin : ∀ U : TrailFamily G k, ∀ M : LollipopEar.RootedCycleRep U r,
      U.score=T.score → (∀ x, U.quota x=T.quota x) → M.cycle=L.cycle → L.tail.length ≤ M.tail.length)
    {v : Fin n} (hv : v ∈ L.tail.support) (hvr : v ≠ r) (hvb : v ≠ L.finish) :
    ∃ j : Fin k, j ≠ L.index ∧ v ∈ (T.walk j).support := by
  classical
  by_contra! hprivate
  have hdegree := private_nonendpoint_degree_two T r L hs hv hvr hvb hprivate
  obtain ⟨u,w,A,B,huv,hvw,hform⟩ := internal_two_edge_form L.tail hv hvr hvb
  have hp : (A.append (Walk.cons huv (Walk.cons hvw B))).IsPath := hform ▸ L.isPath
  have huwNe : u ≠ w := by
    intro heq
    have hn := (Walk.cons_isPath_iff huv _).mp hp.of_append_right |>.2
    exact hn (by simp [heq])
  obtain ⟨_,s,t,hst,hN,hstG⟩ := DegreeTwoReduction.degree_two_triangle hsmall hG hfail hdegree
  have hu : u=s ∨ u=t := (show u ∈ ({s,t} : Set (Fin n)) from hN ▸ huv.symm)
  have hw : w=s ∨ w=t := (show w ∈ ({s,t} : Set (Fin n)) from hN ▸ hvw)
  have huw : G.Adj u w := by
    rcases hu with rfl|rfl <;> rcases hw with rfl|rfl
    · exact (huwNe rfl).elim
    · exact hstG
    · exact hstG.symm
    · exact (huwNe rfl).elim
  have hwr : w ≠ r := by
    intro heq
    have hp' : ((A.concat huv).append (Walk.cons hvw B)).IsPath := by rwa [Walk.concat_append]
    exact (hp'.ne_of_mem_support_of_append hvr.symm (A.concat huv).start_mem_support
      (by simp only [Walk.support_cons,List.mem_cons]; exact Or.inr (heq ▸ B.start_mem_support))) rfl
  have hwC : w ∉ L.cycle.support := by
    intro hw
    exact hwr (L.inter w hw (by rw [hform]; simp))
  have hnot : s(u,w) ∉ (T.walk L.index).toSubgraph.edgeSet := by
    intro he
    rw [L.subgraph,Walk.toSubgraph_append,Subgraph.edgeSet_sup] at he
    rcases he with he|he
    · exact hwC (Walk.mem_support_of_adj_toSubgraph he.symm)
    · rw [Walk.mem_edges_toSubgraph,hform] at he
      exact tail_ear_chord_not_mem A B huv hvw huw hp he
  obtain ⟨j,hj⟩ := (T.cover s(u,w)).mp huw
  have hij : L.index ≠ j := by intro heq; subst j; exact hnot hj
  exact hprivate j hij.symm (shortest_tail_no_fresh_ear T r L hs hmin j hij A B huv hvw huw hform
    ((T.walk j).mem_edges_toSubgraph.mp hj))

/-- Cycle minimization and tail minimization are compatible with the previous
minimum-quota-energy choice: the second optimization fixes the cycle itself. -/
lemma exists_shortest_rooted_structure {n k : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G k) (r : Fin n) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (hroot : HasRoot T r)
    (hdeg : 3 ≤ Nat.card (G.neighborSet r)) :
    ∃ U : TrailFamily G k, ∃ L : LollipopEar.RootedCycleRep U r,
      U.score=T.score ∧ (∀ z, U.quota z=T.quota z) ∧
      RootEnergy.quotaEnergy U=RootEnergy.quotaEnergy T ∧ HasRoot U r ∧
      (L.cycle.length=3 ∨ ∀ x ∈ L.cycle.support, 3 ≤ Nat.card (G.neighborSet x)) ∧
      (∀ W : TrailFamily G k, ∀ M : LollipopEar.RootedCycleRep W r,
        W.score=U.score → (∀ z, W.quota z=U.quota z) → L.cycle.length ≤ M.cycle.length) ∧
      (∀ W : TrailFamily G k, ∀ M : LollipopEar.RootedCycleRep W r,
        W.score=U.score → (∀ z, W.quota z=U.quota z) → M.cycle=L.cycle → L.tail.length ≤ M.tail.length) := by
  obtain ⟨S,N,hSs,hSq,hSE,_,hcases,hmin⟩ := LollipopEar.exists_shortest_rooted_cycle_structure
    hsmall hG hfail T r hs hm hroot hdeg
  obtain ⟨U,L,hUs,hUq,hC,hTail⟩ := exists_shortest_tail S r N
  have hUE : RootEnergy.quotaEnergy U=RootEnergy.quotaEnergy S := by
    apply Finset.sum_congr rfl
    intro z _
    rw [hUq]
  refine ⟨U,L,hUs.trans hSs,fun z ↦ (hUq z).trans (hSq z),hUE.trans hSE,L.hasRoot,?_,?_,hTail⟩
  · rw [hC]
    exact hcases
  · intro W M hWs hWq
    rw [hC]
    exact hmin W M (hWs.trans hUs) (fun z ↦ (hWq z).trans (hUq z))

lemma missing_normal_degree_bound {k : ℕ} (T : TrailFamily G k) (r : V)
    (L : LollipopEar.RootedCycleRep T r) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    {v : V} (hv : v ∉ (MemberExpansion.selectedGraph T (Finset.univ.erase L.index)).support) :
    Nat.card (G.neighborSet v) ≤ if v=r then 3 else 2 := by
  classical
  have hnone := NilSlot.max_score_nonpath_no_nil T hm ⟨L.index,L.member_not_path⟩
  have hindices (j : Fin k) (hj : v ∈ (T.walk j).support) : j=L.index := by
    by_contra hji
    apply hv
    rw [MemberExpansion.selected_support_eq T _ (fun j _ ↦ hnone j)]
    exact ⟨j,by simp [hji],hj⟩
  have hcard : (Finset.univ.filter fun j ↦ v ∈ (T.walk j).support).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro j hj l hl
    exact (hindices j (Finset.mem_filter.mp hj).2).trans (hindices l (Finset.mem_filter.mp hl).2).symm
  have hh := RootCapacity.rooted_incidence T r hs L.hasRoot v
  split_ifs with hvr
  · subst v
    have hpos := RootEnergy.root_quota_pos L.hasRoot
    simp only [↓reduceIte] at hh
    omega
  · have hrne : r ≠ v := fun h ↦ hvr h.symm
    rw [if_neg hrne] at hh
    omega

lemma normal_support_spanning_of_min_degree_four {k : ℕ} (T : TrailFamily G k) (r : V)
    (L : LollipopEar.RootedCycleRep T r) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hdegree : ∀ v, 4 ≤ Nat.card (G.neighborSet v)) :
    (MemberExpansion.selectedGraph T (Finset.univ.erase L.index)).support=Set.univ := by
  apply Set.eq_univ_of_forall
  intro v
  by_contra hv
  have hh := missing_normal_degree_bound T r L hs hm hv
  have hd := hdegree v
  split_ifs at hh <;> omega

lemma odd_normal_support_spanning {n k : ℕ} (hsmall : VertexCritical.SmallerOrders n) (ho : Odd n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G k) (r : Fin n) (L : LollipopEar.RootedCycleRep T r)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) :
    (MemberExpansion.selectedGraph T (Finset.univ.erase L.index)).support=Set.univ :=
  normal_support_spanning_of_min_degree_four T r L hs hm (fun v ↦
    (by have := DegreeFourReduction.min_degree_five_of_odd_failure hsmall ho hG hfail v; omega))

end Erdos583TailEarDevelopment
