import Submission.OddTailComponent

/-! Arbitrary-length private ear exchange in an attached tail, preserving the
literal cycle and every endpoint quota. -/
namespace Erdos583LongTailEarDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.QuotaRooted
open Erdos583Work.LollipopEar Erdos583LongLollipopEarDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false
variable {V : Type*} {G : SimpleGraph V}

lemma shortcut_support_subset {r b u v : V} (A : G.Walk r u) (R : G.Walk u v) (B : G.Walk v b)
    (h : G.Adj u v) :
    (A.append (Walk.cons h B)).support ⊆ (A.append (R.append B)).support := by
  intro x hx
  simp only [Walk.mem_support_append_iff,Walk.support_cons,List.mem_cons] at hx ⊢
  rcases hx with hx|rfl|hx
  · exact Or.inl hx
  · exact Or.inr (Or.inl R.start_mem_support)
  · exact Or.inr (Or.inr hx)

lemma shortcut_isPath {r b u v : V} (A : G.Walk r u) (R : G.Walk u v) (B : G.Walk v b)
    (h : G.Adj u v) (hp : (A.append (R.append B)).IsPath) :
    (A.append (Walk.cons h B)).IsPath := by
  induction A with
  | nil =>
    simp only [Walk.nil_append] at hp ⊢
    apply Walk.IsPath.cons hp.of_append_right
    intro hu
    exact (hp.ne_of_mem_support_of_append h.ne R.start_mem_support hu) rfl
  | cons hA A ih =>
    rw [Walk.cons_append,Walk.cons_isPath_iff] at hp ⊢
    exact ⟨ih R h hp.1,fun hx ↦ hp.2 (shortcut_support_subset A R B h hx)⟩

lemma long_tail_exchange [Fintype V] {r b a d u v : V}
    (C : G.Walk r r) (A : G.Walk r u) (R : G.Walk u v) (B : G.Walk v b)
    (h : G.Adj u v) (hp : (A.append (R.append B)).IsPath)
    (hinter : ∀ z ∈ C.support, z ∈ (A.append (R.append B)).support → z=r)
    (P : G.Walk a d) (hP : P.IsPath) (he : s(u,v) ∈ P.edges)
    (hfresh : ∀ z ∈ R.support, z ≠ u → z ≠ v → z ∉ P.support)
    (hd : Disjoint (C.append (A.append (R.append B))).toSubgraph.edgeSet P.toSubgraph.edgeSet) :
    ∃ Q : G.Walk a d, Q.IsPath ∧
      Disjoint (C.append (A.append (Walk.cons h B))).toSubgraph.edgeSet Q.toSubgraph.edgeSet ∧
      (C.append (A.append (Walk.cons h B))).toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet=
        (C.append (A.append (R.append B))).toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet := by
  obtain ⟨Q,hQ,hQe⟩ := path_expand_fresh_path P hP R hp.of_append_right.of_append_left he hfresh
  let E := C.toSubgraph.edgeSet ∪ A.toSubgraph.edgeSet ∪ B.toSubgraph.edgeSet
  have hOld : (C.append (A.append (R.append B))).toSubgraph.edgeSet=E ∪ R.toSubgraph.edgeSet := by
    simp only [E,Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    ac_rfl
  have hNew : (C.append (A.append (Walk.cons h B))).toSubgraph.edgeSet=E ∪ {s(u,v)} := by
    ext e
    simp only [E,Walk.mem_edges_toSubgraph,Walk.edges_append,Walk.edges_cons,List.mem_append,
      List.mem_cons,Set.mem_union,Set.mem_singleton_iff]
    tauto
  have hER : Disjoint E R.toSubgraph.edgeSet := by
    have hCR := edge_disjoint_of_one_common_vertex C (A.append (R.append B)) hinter
    have hAR := RootedTailSystem.append_trail_disjoint hp.isTrail
    have hRB := RootedTailSystem.append_trail_disjoint hp.of_append_right.isTrail
    simp only [Walk.toSubgraph_append,Subgraph.edgeSet_sup] at hCR hAR
    exact disjoint_sup_left.mpr ⟨disjoint_sup_left.mpr
      ⟨(disjoint_sup_right.mp (disjoint_sup_right.mp hCR).2).1,(disjoint_sup_right.mp hAR).1⟩,hRB.symm⟩
  have hEP : Disjoint E P.toSubgraph.edgeSet := by rw [hOld] at hd; exact (disjoint_sup_left.mp hd).1
  have heR : s(u,v) ∉ R.toSubgraph.edgeSet := by
    rw [hOld] at hd
    exact fun hh ↦ Set.disjoint_left.mp (disjoint_sup_left.mp hd).2 hh (P.mem_edges_toSubgraph.mpr he)
  refine ⟨Q,hQ,?_,?_⟩
  · rw [hNew,hQe]
    apply Set.disjoint_left.mpr
    intro e hN hQ
    rcases hN with hN|hN <;> rcases hQ with hQ|hQ
    · exact Set.disjoint_left.mp hEP hN hQ.1
    · exact Set.disjoint_left.mp hER hN hQ
    · exact hQ.2 hN
    · exact heR ((Set.mem_singleton_iff.mp hN) ▸ hQ)
  · rw [hNew,hOld,hQe]
    have heP := P.mem_edges_toSubgraph.mpr he
    ext e
    simp only [Set.mem_union,Set.mem_diff,Set.mem_singleton_iff]
    by_cases hh : e=s(u,v)
    · subst e
      simp only [heP,eq_self,true_or,or_true,not_true_eq_false,and_false]
    · tauto

lemma shorten_tail_at_fresh_long_ear [Fintype V] {k : ℕ} (T : TrailFamily G k) (r : V)
    (L : LollipopEar.RootedCycleRep T r) (hs : T.score+1=G.edgeSet.ncard+k)
    (j : Fin k) (hij : L.index ≠ j) {u v : V}
    (A : G.Walk r u) (E : G.Walk u v) (B : G.Walk v L.finish)
    (h : G.Adj u v)
    (hform : L.tail=A.append (E.append B))
    (he : s(u,v) ∈ (T.walk j).edges)
    (hfresh : ∀ z ∈ E.support, z ≠ u → z ≠ v → z ∉ (T.walk j).support) :
    ∃ U : TrailFamily G k, ∃ M : LollipopEar.RootedCycleRep U r,
      U.score=T.score ∧ (∀ x, U.quota x=T.quota x) ∧ M.cycle=L.cycle ∧
      M.tail.length+E.length=L.tail.length+1 := by
  classical
  let R := A.append (Walk.cons h B)
  have hp : (A.append (E.append B)).IsPath := hform ▸ L.isPath
  have hR : R.IsPath := shortcut_isPath A E B h hp
  have hint (z : V) (hz : z ∈ L.cycle.support) (hzR : z ∈ R.support) : z=r := by
    apply L.inter z hz
    rw [hform]
    exact shortcut_support_subset A E B h hzR
  have hRtrail := trail_append_of_disjoint L.isCycle.isTrail hR.isTrail
    (LollipopEar.edge_disjoint_of_one_common_vertex L.cycle R hint)
  have hP := (T.one_defect_other_paths hs L.index L.member_not_path).2 j hij.symm
  have hd : Disjoint (L.cycle.append (A.append (E.append B))).toSubgraph.edgeSet
      (T.walk j).toSubgraph.edgeSet := by
    rw [←hform,←L.subgraph]
    exact T.disjoint hij
  obtain ⟨Q,hQ,hsep,hcover⟩ := long_tail_exchange L.cycle A E B h hp
    (by intro z hz hzS; exact L.inter z hz (hform.symm ▸ hzS)) (T.walk j) hP he hfresh hd
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
  · change R.length+E.length=L.tail.length+1
    rw [hform]
    simp [R]
    omega

lemma no_long_tail_ear [Fintype V] {k : ℕ} (T : TrailFamily G k) (r : V)
    (L : RootedCycleRep T r) (hs : T.score+1=G.edgeSet.ncard+k)
    (hmin : ∀ U : TrailFamily G k, ∀ M : RootedCycleRep U r,
      U.score=T.score → (∀ x, U.quota x=T.quota x) → M.cycle=L.cycle → L.tail.length ≤ M.tail.length)
    (j : Fin k) (hij : L.index ≠ j) {u v : V}
    (A : G.Walk r u) (E : G.Walk u v) (B : G.Walk v L.finish) (h : G.Adj u v)
    (hform : L.tail=A.append (E.append B)) (hE : 2 ≤ E.length)
    (he : s(u,v) ∈ (T.walk j).edges)
    (hfresh : ∀ z ∈ E.support, z ≠ u → z ≠ v → z ∉ (T.walk j).support) : False := by
  obtain ⟨U,M,hUs,hUq,hC,hLen⟩ := shorten_tail_at_fresh_long_ear T r L hs j hij A E B h hform he hfresh
  have hh := hmin U M hUs hUq hC
  omega

end Erdos583LongTailEarDevelopment
