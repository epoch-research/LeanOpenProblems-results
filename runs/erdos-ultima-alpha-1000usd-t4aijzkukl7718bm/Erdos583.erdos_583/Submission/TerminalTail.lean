import Submission.Work

/-! Terminal-edge transfer for a rooted lollipop, preserving all endpoint
quotas and the literal rooted cycle. -/
namespace Erdos583TerminalTailDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open scoped Classical
set_option maxHeartbeats 1800000

lemma replace_two_finishes_general {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i j : Fin k) (hij : i ≠ j) (u v : V)
    (p : G.Walk (T.start i) u) (q : G.Walk (T.start j) v)
    (hp : p.IsTrail) (hq : q.IsTrail)
    (hpq : Disjoint p.toSubgraph.edgeSet q.toSubgraph.edgeSet)
    (hu : p.toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet =
      (T.walk i).toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet) :
    ∃ S : TrailFamily G k,
      (S.walk i).toSubgraph = p.toSubgraph ∧
      (S.walk j).toSubgraph = q.toSubgraph ∧
      (∀ l, l ≠ i → l ≠ j → (S.walk l).toSubgraph = (T.walk l).toSubgraph) ∧
      S.start = T.start ∧ S.finish = (fun l ↦ if l=i then u else if l=j then v else T.finish l) ∧
      S.score + (T.walk i).toSubgraph.verts.ncard + (T.walk j).toSubgraph.verts.ncard =
        T.score + p.toSubgraph.verts.ncard + q.toSubgraph.verts.ncard ∧
      ∀ x, S.quota x + (if T.finish i=x then 1 else 0) + (if T.finish j=x then 1 else 0) =
        T.quota x + (if u=x then 1 else 0) + (if v=x then 1 else 0) := by
  obtain ⟨R,hRs,hRq,hR⟩ := orient T (fun _ ↦ true)
  have hRa (l) : R.start l=T.finish l := (hR l).1
  have hRb (l) : R.finish l=T.start l := (hR l).2.1
  let P := p.reverse.copy rfl (hRb i).symm
  let Q := q.reverse.copy rfl (hRb j).symm
  have hPe : P.toSubgraph=p.toSubgraph := by simp only [P,NormalTrailSystem.walk_copy_subgraph,Walk.toSubgraph_reverse]
  have hQe : Q.toSubgraph=q.toSubgraph := by simp only [Q,NormalTrailSystem.walk_copy_subgraph,Walk.toSubgraph_reverse]
  have hP : P.IsTrail := by simpa [P] using hp.reverse
  have hQ : Q.IsTrail := by simpa [Q] using hq.reverse
  obtain ⟨A,hAi,hAj,hAl,hAa,hAb,hAs,hAq⟩ := replace_two_starts_general R i j hij u v P Q hP hQ
    (by rw [hPe,hQe]; exact hpq)
    (by rw [hPe,hQe,(hR i).2.2,(hR j).2.2]; exact hu)
  obtain ⟨S,hSs,hSq,hS⟩ := orient A (fun _ ↦ true)
  refine ⟨S,(hS i).2.2.trans (hAi.trans hPe),(hS j).2.2.trans (hAj.trans hQe),?_,?_,?_,?_,?_⟩
  · intro l hli hlj
    exact (hS l).2.2.trans ((hAl l hli hlj).trans (hR l).2.2)
  · funext l
    exact (hS l).1.trans ((congrFun hAb l).trans (hRb l))
  · funext l
    have hh := (hS l).2.1
    simpa only [hAa,hRa] using hh
  · rw [hPe,hQe,(hR i).2.2,(hR j).2.2,hRs] at hAs
    rwa [hSs]
  · intro x
    have hh := hAq x
    rw [hRa,hRa,hRq] at hh
    rwa [hSq]

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}

lemma shorten_terminal_tail (T : TrailFamily G k) (r : V)
    (L : LollipopEar.RootedCycleRep T r) (hs : T.score+1=G.edgeSet.ncard+k)
    (j : Fin k) (hij : L.index ≠ j) {w : V}
    (R : G.Walk r w) (h : G.Adj w L.finish) (hform : L.tail=R.concat h)
    (hj : T.finish j=w) (hbj : L.finish ∉ (T.walk j).support) :
    ∃ U : TrailFamily G k, ∃ M : LollipopEar.RootedCycleRep U r,
      U.score=T.score ∧ (∀ x, U.quota x=T.quota x) ∧ M.cycle=L.cycle ∧
      M.tail.length+1=L.tail.length := by
  classical
  have hR : R.IsPath := (Walk.concat_isPath_iff h).mp (hform ▸ L.isPath) |>.1
  have hint (z : V) (hz : z ∈ L.cycle.support) (hzR : z ∈ R.support) : z=r := by
    apply L.inter z hz
    rw [hform,Walk.support_concat,List.concat_eq_append,List.mem_append,List.mem_singleton]
    exact Or.inl hzR
  have hP := (T.one_defect_other_paths hs L.index L.member_not_path).2 j hij.symm
  let Q := (T.walk j).concat (hj.symm ▸ h)
  have hQ : Q.IsPath := (Walk.concat_isPath_iff _).mpr ⟨hP,hbj⟩
  let P := (L.cycle.append R).copy L.start_eq.symm rfl
  have hPe : P.toSubgraph=(L.cycle.append R).toSubgraph := NormalTrailSystem.walk_copy_subgraph _ _ _
  have hPt := trail_append_of_disjoint L.isCycle.isTrail hR.isTrail
    (LollipopEar.edge_disjoint_of_one_common_vertex L.cycle R hint)
  have hP' : P.IsTrail := by simpa only [P,Walk.isTrail_copy] using hPt
  have hold := trail_append_of_disjoint L.isCycle.isTrail L.isPath.isTrail
    (LollipopEar.edge_disjoint_of_one_common_vertex L.cycle L.tail L.inter)
  have hPeOld : P.toSubgraph.edgeSet ⊆ (T.walk L.index).toSubgraph.edgeSet := by
    rw [hPe,L.subgraph,hform]
    intro e he
    simp only [Walk.mem_edges_toSubgraph,Walk.edges_append,Walk.edges_concat,List.mem_append,List.concat_eq_append,List.mem_append,List.mem_singleton] at he ⊢
    tauto
  have hnew : s(w,L.finish) ∉ P.toSubgraph.edgeSet := by
    have htrail : ((L.cycle.append R).concat h).IsTrail := by
      simpa only [hform,Walk.append_concat] using hold
    rw [hPe]
    intro he
    have hn := htrail.edges_nodup
    rw [Walk.edges_concat,List.nodup_concat] at hn
    exact hn.1 ((L.cycle.append R).mem_edges_toSubgraph.mp he)
  have hQe : Q.toSubgraph.edgeSet=insert s(w,L.finish) (T.walk j).toSubgraph.edgeSet := by
    ext e
    simp only [Q,Walk.mem_edges_toSubgraph,Walk.edges_concat,List.concat_eq_append,List.mem_append,List.mem_singleton,Set.mem_insert_iff,hj]
    tauto
  have hd : Disjoint P.toSubgraph.edgeSet Q.toSubgraph.edgeSet := by
    rw [hQe]
    exact Set.disjoint_insert_right.mpr ⟨hnew,(T.disjoint hij).mono_left hPeOld⟩
  have heq : P.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet=
      (T.walk L.index).toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet := by
    rw [hPe,hQe,L.subgraph,hform]
    ext e
    simp only [Walk.mem_edges_toSubgraph,Walk.edges_append,Walk.edges_concat,List.mem_append,List.concat_eq_append,List.mem_append,List.mem_singleton,
      Set.mem_union,Set.mem_insert_iff]
    tauto
  obtain ⟨U,hUi,_,_,hUa,hUb,hUs,hUq⟩ := replace_two_finishes_general T L.index j hij w L.finish P Q hP' hQ.isTrail hd heq
  have ha : U.start L.index=r := (congrFun hUa L.index).trans L.start_eq
  have hb : U.finish L.index=w := by rw [hUb]; simp
  let M : LollipopEar.RootedCycleRep U r :=
    ⟨L.index,w,ha,hb,L.cycle,R,L.isCycle,hR,hint,hUi.trans hPe⟩
  have hlen : (T.walk L.index).length=(L.cycle.append L.tail).length := by
    rw [←trail_edgeSet_ncard _ (T.isTrail L.index),L.subgraph,trail_edgeSet_ncard _ hold]
  have hvc : (T.walk L.index).toSubgraph.verts.ncard=(T.walk L.index).length := by
    rw [L.subgraph,LollipopEar.lollipop_vertex_card L.cycle L.isCycle L.tail L.isPath L.inter,hlen]
  have hpc : P.toSubgraph.verts.ncard=P.length := by
    rw [hPe,LollipopEar.lollipop_vertex_card L.cycle L.isCycle R hR hint]
    simp [P]
  have hsum := congrArg Set.ncard heq
  rw [Set.ncard_union_eq hd,Set.ncard_union_eq (T.disjoint hij),trail_edgeSet_ncard _ hP',
    trail_edgeSet_ncard _ hQ.isTrail,trail_edgeSet_ncard _ (T.isTrail L.index),
    trail_edgeSet_ncard _ (T.isTrail j)] at hsum
  rw [hvc,hpc,(walk_vertex_ncard_eq_iff _).mpr hP,(walk_vertex_ncard_eq_iff _).mpr hQ] at hUs
  refine ⟨U,M,by omega,?_,rfl,?_⟩
  · intro x
    have hh := hUq x
    rw [L.finish_eq,hj] at hh
    omega
  · change R.length+1=L.tail.length
    simp [hform]


lemma shorten_terminal_tail_at_endpoint (T : TrailFamily G k) (r : V)
    (L : LollipopEar.RootedCycleRep T r) (hs : T.score+1=G.edgeSet.ncard+k)
    (j : Fin k) (hij : L.index ≠ j) {w : V}
    (R : G.Walk r w) (h : G.Adj w L.finish) (hform : L.tail=R.concat h)
    (hj : w=T.start j ∨ w=T.finish j) (hbj : L.finish ∉ (T.walk j).support) :
    ∃ U : TrailFamily G k, ∃ M : LollipopEar.RootedCycleRep U r,
      U.score=T.score ∧ (∀ x, U.quota x=T.quota x) ∧ M.cycle=L.cycle ∧
      M.tail.length+1=L.tail.length := by
  classical
  obtain ⟨A,hAs,hAq,hA⟩ := orient T (fun l ↦ decide (l=j ∧ w=T.start j))
  have hAi : A.start L.index=r := by simpa [hij,L.start_eq] using (hA L.index).1
  have hAb : A.finish L.index=L.finish := by simpa [hij,L.finish_eq] using (hA L.index).2.1
  let N : LollipopEar.RootedCycleRep A r :=
    ⟨L.index,L.finish,hAi,hAb,L.cycle,L.tail,L.isCycle,L.isPath,L.inter,(hA L.index).2.2.trans L.subgraph⟩
  have hAj : A.finish j=w := by
    have hh := (hA j).2.1
    rcases hj with hj|hj
    · simpa [hj] using hh
    · by_cases ha : w=T.start j
      · simpa [ha] using hh
      · have hh' : A.finish j=T.finish j := by simpa [ha] using hh
        exact hh'.trans hj.symm
  have hbA : N.finish ∉ (A.walk j).support := by
    change L.finish ∉ (A.walk j).support
    rw [←Walk.mem_verts_toSubgraph,(hA j).2.2,Walk.mem_verts_toSubgraph]
    exact hbj
  obtain ⟨U,M,hUs,hUq,hC,hLen⟩ := shorten_terminal_tail A r N (by rw [hAs]; exact hs)
    j hij R h hform hAj hbA
  exact ⟨U,M,hUs.trans hAs,fun x ↦ (hUq x).trans (hAq x),hC,hLen⟩

omit [Fintype V] in
lemma nonnil_last_edge {r b : V} (P : G.Walk r b) (hn : ¬P.Nil) :
    ∃ w, ∃ R : G.Walk r w, ∃ h : G.Adj w b, P=R.concat h := by
  cases P with
  | nil => exact (hn Walk.Nil.nil).elim
  | cons h P => exact Walk.exists_cons_eq_concat h P

/-- A shortest tail with a private final leaf cannot have an internal
penultimate vertex: the bridge parity forces an endpoint there, and the
terminal edge can be transferred to its member. -/
lemma shortest_private_finish_tail_length_one {n k : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G k) (r : Fin n) (L : LollipopEar.RootedCycleRep T r)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hmin : ∀ U : TrailFamily G k, ∀ M : LollipopEar.RootedCycleRep U r,
      U.score=T.score → (∀ x, U.quota x=T.quota x) → M.cycle=L.cycle → L.tail.length ≤ M.tail.length)
    (hbr : L.finish ≠ r)
    (hb : L.finish ∉ (MemberExpansion.selectedGraph T (Finset.univ.erase L.index)).support) :
    L.tail.length=1 := by
  classical
  have hn : ¬L.tail.Nil := fun he ↦ hbr he.eq.symm
  obtain ⟨w,R,h,hform⟩ := nonnil_last_edge L.tail hn
  have hbG : L.finish ∈ G.support := G.mem_support.mpr ⟨w,h.symm⟩
  have hleaf := NormalRemainder.missing_finish_leaf T r L hs hm hbG hbr hb
  have hN : ∀ x, G.Adj L.finish x → x=w := by
    obtain ⟨a,ha,haa⟩ := LeafPairReduction.leaf_data hleaf
    intro x hx
    exact (haa x hx).trans (haa w h.symm).symm
  have hbridge := CutVertexParity.leaf_edge_bridge h.symm hN
  have hodd := (BridgeParityReduction.bridge_endpoints_odd_of_failure hsmall hG hfail hbridge).2
  have hR : R.IsPath := (Walk.concat_isPath_iff h).mp (hform ▸ L.isPath) |>.1
  by_cases hwr : w=r
  · have hzero : R.length=0 := by
      subst w
      rw [(Walk.isPath_iff_eq_nil R).mp hR]
      rfl
    simp [hform,hzero]
  · have hq : 0 < T.quota w := ((QuotaParity.quota_odd_iff T w).mpr hodd).pos
    obtain ⟨j,hj⟩ := DeletionEndpoint.endpoint_of_positive_quota T hq
    have hij : L.index ≠ j := by
      rintro rfl
      rcases hj with hj|hj
      · exact hwr (hj.trans L.start_eq)
      · exact h.ne (hj.trans L.finish_eq)
    have hnone := NilSlot.max_score_nonpath_no_nil T hm ⟨L.index,L.member_not_path⟩
    have hbj : L.finish ∉ (T.walk j).support := by
      intro hx
      apply hb
      rw [MemberExpansion.selected_support_eq T _ (fun l _ ↦ hnone l)]
      exact ⟨j,by simp [hij.symm],hx⟩
    obtain ⟨U,M,hUs,hUq,hC,hLen⟩ := shorten_terminal_tail_at_endpoint T r L hs j hij R h hform hj hbj
    have hle := hmin U M hUs hUq hC
    omega

end Erdos583TerminalTailDevelopment
