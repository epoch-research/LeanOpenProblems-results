import Submission.Work

/-! A fresh two-edge ear can exchange places with a chord in another path.
This shortens a cycle without changing the path/trail incidence score. -/
namespace Erdos583CycleEarDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open scoped Classical
set_option maxHeartbeats 1600000

lemma path_expand_fresh_ear {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b u r v : V} (P : G.Walk a b) (hP : P.IsPath)
    (hur : G.Adj u r) (hrv : G.Adj r v) (huv : u ≠ v)
    (he : s(u,v) ∈ P.edges) (hfresh : r ∉ P.support) :
    ∃ Q : G.Walk a b, Q.IsPath ∧
      Q.toSubgraph.edgeSet=(P.toSubgraph.edgeSet \ {s(u,v)}) ∪ {s(u,r),s(r,v)} := by
  classical
  let H := P.toSubgraph.spanningCoe
  have hedge : ∀ e ∈ P.edges, e ∈ H.edgeSet := fun e he ↦ P.mem_edges_toSubgraph.mpr he
  let P' := P.transfer H hedge
  let R : G.Walk u v := .cons hur (.cons hrv .nil)
  have hR : R.IsPath := by simp [R,Walk.cons_isPath_iff,hur.ne,hrv.ne,huv]
  have hf : ∀ x ∈ R.support, x ≠ u → x ≠ v → x ∉ H.support := by
    intro x hx hxu hxv hxH
    have hxr : x=r := by simpa [R,Walk.support,hxu,hxv] using hx
    subst x
    obtain ⟨y,hy⟩ := (mem_support H).mp hxH
    exact hfresh (Walk.mem_support_of_adj_toSubgraph (show P.toSubgraph.Adj r y from hy))
  obtain ⟨Q,hQ,hQe⟩ := path_expand_edge R hR
    ((H.deleteEdges_le _).trans P.toSubgraph.spanningCoe_le) hf P' (hP.transfer hedge)
  refine ⟨Q,hQ,?_⟩
  simpa only [P',Walk.edges_transfer,Walk.edgeSet_toSubgraph,he,if_true,R,Walk.edges_cons,
    Walk.edges_nil,Set.setOf_mem_eq,List.mem_cons,List.not_mem_nil,or_false] using hQe

lemma cycle_ear_exchange {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b r u v : V} (hru : G.Adj r u) (hvr : G.Adj v r) (R : G.Walk u v)
    (hC : (Walk.cons hru (R.concat hvr)).IsCycle)
    (P : G.Walk a b) (hP : P.IsPath) (huv : G.Adj u v)
    (he : s(u,v) ∈ P.edges) (hr : r ∉ P.support)
    (hd : Disjoint (Walk.cons hru (R.concat hvr)).toSubgraph.edgeSet P.toSubgraph.edgeSet) :
    (Walk.cons huv R.reverse).IsCycle ∧
    ∃ Q : G.Walk a b, Q.IsPath ∧
      Disjoint (Walk.cons huv R.reverse).toSubgraph.edgeSet Q.toSubgraph.edgeSet ∧
      (Walk.cons huv R.reverse).toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet =
        (Walk.cons hru (R.concat hvr)).toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet ∧
      (Walk.cons huv R.reverse).length+1=(Walk.cons hru (R.concat hvr)).length := by
  classical
  have hRp : R.IsPath := ((Walk.cons_isCycle_iff _ _).mp hC).1.of_append_left
  have heR : s(u,v) ∉ R.edges := by
    intro hh
    apply Set.disjoint_left.mp hd _ (P.mem_edges_toSubgraph.mpr he)
    simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.concat_eq_append,Walk.edges_append,
      List.mem_cons,List.mem_append]
    exact Or.inr (Or.inl hh)
  have hnewC : (Walk.cons huv R.reverse).IsCycle := by
    rw [Walk.cons_isCycle_iff]
    exact ⟨hRp.reverse,by simpa only [Walk.edges_reverse,List.mem_reverse] using heR⟩
  obtain ⟨Q,hQ,hQe⟩ := path_expand_fresh_ear P hP hru.symm hvr.symm huv.ne he hr
  have hRe : (Walk.cons huv R.reverse).toSubgraph.edgeSet={s(u,v)} ∪ R.toSubgraph.edgeSet := by
    ext e
    simp
  have hCe : (Walk.cons hru (R.concat hvr)).toSubgraph.edgeSet=
      {s(u,r),s(r,v)} ∪ R.toSubgraph.edgeSet := by
    ext e
    simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.concat_eq_append,Walk.edges_append,
      Walk.edges_nil,List.mem_cons,List.mem_append,List.not_mem_nil,or_false,
      Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := r) (b := u),
      Sym2.eq_swap (a := v) (b := r)]
    tauto
  have hdR : Disjoint R.toSubgraph.edgeSet P.toSubgraph.edgeSet := by
    rw [hCe] at hd
    exact (disjoint_sup_left.mp hd).2
  have hdEar : Disjoint R.toSubgraph.edgeSet ({s(u,r),s(r,v)} : Set (Sym2 V)) := by
    have ht := hC.isTrail.edges_nodup
    simp only [Walk.edges_cons,Walk.concat_eq_append,Walk.edges_append,Walk.edges_cons,
      Walk.edges_nil,List.nodup_cons,List.nodup_append,List.not_mem_nil,not_false_eq_true] at ht
    apply Set.disjoint_left.mpr
    intro e heR heEar
    have hm : e ∈ R.edges := R.mem_edges_toSubgraph.mp heR
    rcases heEar with he'|he'
    · have he' : e=s(u,r) := he'
      exact ht.1 (List.mem_append.mpr (Or.inl (by simpa only [he',Sym2.eq_swap] using hm)))
    · have he' : e=s(r,v) := he'
      exact ht.2.2.2 e hm s(v,r) (by simp) (by simp only [he',Sym2.eq_swap])
  refine ⟨hnewC,Q,hQ,?_,?_,by simp [Walk.length_concat]⟩
  · rw [hRe,hQe]
    apply Set.disjoint_left.mpr
    intro e heC heQ
    rcases heC with heC|heC <;> rcases heQ with heQ|heQ
    · exact heQ.2 heC
    · have heC' : e=s(u,v) := heC
      rcases heQ with heQ|heQ
      · have heQ' : e=s(u,r) := heQ
        have hh := heC'.symm.trans heQ'
        rcases Sym2.eq_iff.mp hh with ⟨_,h⟩|⟨_,h⟩
        · exact hvr.ne h
        · exact huv.ne.symm h
      · have heQ' : e=s(r,v) := heQ
        have hh := heC'.symm.trans heQ'
        rcases Sym2.eq_iff.mp hh with ⟨h,_⟩|⟨h,_⟩
        · exact hru.ne h.symm
        · exact huv.ne h
    · exact Set.disjoint_left.mp hdR heC heQ.1
    · exact Set.disjoint_left.mp hdEar heC heQ
  · rw [hRe,hQe,hCe]
    ext e
    simp only [Set.mem_union,Set.mem_diff,Set.mem_insert_iff,Set.mem_singleton_iff]
    by_cases hh : e=s(u,v)
    · subst e
      simp [he]
    · tauto

lemma cycle_member_not_path {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (he : (T.walk i).toSubgraph=C.toSubgraph) : ¬(T.walk i).IsPath := by
  intro hp
  have hv := (walk_vertex_ncard_eq_iff (T.walk i)).mpr hp
  have hl : (T.walk i).length=C.length := by
    rw [←trail_edgeSet_ncard _ (T.isTrail i),he,trail_edgeSet_ncard _ hC.isTrail]
  rw [he,Walk.verts_toSubgraph,cycle_support_ncard hC,hl] at hv
  omega

lemma replace_cycle_and_path {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i j : Fin k) (hij : i ≠ j)
    {r s a b : V} (C : G.Walk r r) (C' : G.Walk s s) (P' : G.Walk a b)
    (hC : C.IsCycle) (hC' : C'.IsCycle) (hP' : P'.IsPath)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) (hj : (T.walk j).IsPath)
    (hd : Disjoint C'.toSubgraph.edgeSet P'.toSubgraph.edgeSet)
    (hc : C'.toSubgraph.edgeSet ∪ P'.toSubgraph.edgeSet =
      C.toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet) :
    ∃ U : TrailFamily G k, U.score=T.score ∧ (U.walk i).toSubgraph=C'.toSubgraph := by
  obtain ⟨U,hUi,_,_,hs⟩ := GeneralPair.replace_two T i j hij s s a b C' P'
    hC'.isTrail hP'.isTrail hd (by simpa only [hi] using hc)
  have hdold : Disjoint C.toSubgraph.edgeSet (T.walk j).toSubgraph.edgeSet := by
    rw [←hi]; exact T.disjoint hij
  have hl := congrArg Set.ncard hc
  rw [Set.ncard_union_eq hd,Set.ncard_union_eq hdold,trail_edgeSet_ncard _ hC'.isTrail,
    trail_edgeSet_ncard _ hP'.isTrail,trail_edgeSet_ncard _ hC.isTrail,
    trail_edgeSet_ncard _ hj.isTrail] at hl
  have hvC : C.toSubgraph.verts.ncard=C.length := by
    rw [Walk.verts_toSubgraph,cycle_support_ncard hC]
  have hvC' : C'.toSubgraph.verts.ncard=C'.length := by
    rw [Walk.verts_toSubgraph,cycle_support_ncard hC']
  rw [hi,hvC,hvC',(walk_vertex_ncard_eq_iff _).mpr hj,
    (walk_vertex_ncard_eq_iff _).mpr hP'] at hs
  exact ⟨U,by omega,hUi⟩

/-- A cycle with a removable two-edge ear is not a shortest whole cycle
among the families with the same incidence score. -/
lemma shorten_cycle_member {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i j : Fin k) (hij : i ≠ j) {r u v : V}
    (hru : G.Adj r u) (hvr : G.Adj v r) (R : G.Walk u v)
    (hC : (Walk.cons hru (R.concat hvr)).IsCycle)
    (hi : (T.walk i).toSubgraph=(Walk.cons hru (R.concat hvr)).toSubgraph)
    (huv : G.Adj u v) (he : s(u,v) ∈ (T.walk j).edges) (hr : r ∉ (T.walk j).support) :
    ∃ U : TrailFamily G k, ∃ C : G.Walk u u, U.score=T.score ∧ C.IsCycle ∧
      (U.walk i).toSubgraph=C.toSubgraph ∧ C.length+1=(Walk.cons hru (R.concat hvr)).length := by
  have hj := (T.one_defect_other_paths hs i (cycle_member_not_path T i _ hC hi)).2 j hij.symm
  have hd : Disjoint (Walk.cons hru (R.concat hvr)).toSubgraph.edgeSet (T.walk j).toSubgraph.edgeSet := by
    rw [←hi]; exact T.disjoint hij
  obtain ⟨hc,Q,hQ,hsep,hcover,hlen⟩ := cycle_ear_exchange hru hvr R hC (T.walk j) hj huv he hr hd
  obtain ⟨U,hUs,hUi⟩ := replace_cycle_and_path T i j hij _ _ Q hC hc hQ hi hj hsep hcover
  exact ⟨U,_,hUs,hc,hUi,hlen⟩

/-- Minimize over all equal-score families, not just over representations
of one fixed cycle subgraph. -/
def ShortestCycle {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (m : ℕ) : Prop :=
  ∀ U : TrailFamily G k, U.score=T.score → ∀ i r (C : G.Walk r r),
    C.IsCycle → (U.walk i).toSubgraph=C.toSubgraph → m ≤ C.length

lemma exists_shortest_cycle {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) {r : V} (C : G.Walk r r)
    (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph) :
    ∃ U : TrailFamily G k, ∃ j r, ∃ D : G.Walk r r,
      U.score=T.score ∧ D.IsCycle ∧ (U.walk j).toSubgraph=D.toSubgraph ∧
      ShortestCycle U D.length := by
  classical
  let P (m : ℕ) := ∃ U : TrailFamily G k, ∃ j r, ∃ D : G.Walk r r,
    U.score=T.score ∧ D.IsCycle ∧ (U.walk j).toSubgraph=D.toSubgraph ∧ D.length=m
  have hex : ∃ m, P m := ⟨C.length,T,i,r,C,rfl,hC,hi,rfl⟩
  obtain ⟨U,j,r,D,hUs,hD,hj,hDl⟩ := Nat.find_spec hex
  refine ⟨U,j,r,D,hUs,hD,hj,?_⟩
  intro W hWs l s E hE hl
  rw [hDl]
  exact Nat.find_min' hex ⟨W,l,s,E,hWs.trans hUs,hE,hl,rfl⟩

lemma other_path_avoids_degree_two_cycle {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i j : Fin k) (hij : i ≠ j) {s r : V}
    (C : G.Walk s s) (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hrC : r ∈ C.support) (hr : Nat.card (G.neighborSet r)=2)
    (hj : (T.walk j).IsPath) (hn : ¬(T.walk j).Nil) : r ∉ (T.walk j).support := by
  have hN : C.toSubgraph.neighborSet r=G.neighborSet r := by
    apply Set.eq_of_subset_of_ncard_le (fun _ hh ↦ C.toSubgraph.adj_sub hh)
    change (G.neighborSet r).ncard ≤ (C.toSubgraph.neighborSet r).ncard
    rw [hC.ncard_neighborSet_toSubgraph_eq_two hrC,←Nat.card_coe_set_eq,hr]
  intro hrj
  obtain ⟨z,hz⟩ := (Set.ncard_pos (Set.toFinite _)).mp (path_neighbor_ncard_pos hj hn hrj)
  have hzG := (T.walk j).toSubgraph.adj_sub hz
  have hzC : C.toSubgraph.Adj r z := by change z ∈ C.toSubgraph.neighborSet r; rw [hN]; exact hzG
  have hzCi : s(r,z) ∈ (T.walk i).toSubgraph.edgeSet := by rw [hi]; exact hzC
  exact Set.disjoint_left.mp (T.disjoint hij) hzCi (show s(r,z) ∈ (T.walk j).toSubgraph.edgeSet from hz)

lemma cycle_two_spokes {V : Type*} {G : SimpleGraph V} {r : V}
    (C : G.Walk r r) (hC : C.IsCycle) :
    ∃ u v, ∃ hru : G.Adj r u, ∃ hvr : G.Adj v r, ∃ R : G.Walk u v,
      C=Walk.cons hru (R.concat hvr) := by
  cases C with
  | nil => exact (hC.not_nil Walk.Nil.nil).elim
  | cons h p =>
    cases p with
    | nil => exact (h.ne rfl).elim
    | cons g q =>
      obtain ⟨v,R,hvr,he⟩ := Walk.exists_cons_eq_concat g q
      exact ⟨_,v,h,hvr,R,congrArg (Walk.cons h) he⟩

lemma path_eq_singleton_of_endpoint_edge {V : Type*} {G : SimpleGraph V} {a b : V}
    (P : G.Walk a b) (hp : P.IsPath) (h : G.Adj a b) (he : s(a,b) ∈ P.edges) :
    P=Walk.cons h Walk.nil := by
  cases P with
  | nil => simp at he
  | @cons a x b g p =>
    have heq : b=x := by simpa only [Walk.snd_cons] using hp.eq_snd_of_mem_edges he
    subst x
    have he' := (Walk.isPath_iff_eq_nil p).mp hp.of_cons
    subst p
    rfl

/-- In a smallest counterexample, a shortest whole cycle in a one-defect
maximum has no ambient degree-two vertex. The conclusion does not say a
whole cycle member must exist. -/
lemma shortest_cycle_no_degree_two {n k : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (hk : Fintype.card (Fin n) ≤ 2*k)
    (i : Fin k) {a : Fin n} (C : G.Walk a a) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) (hmin : ShortestCycle T C.length)
    {r : Fin n} (hrC : r ∈ C.support) (hr : Nat.card (G.neighborSet r)=2) : False := by
  classical
  let D := C.rotate hrC
  have hD : D.IsCycle := hC.rotate hrC
  have hDi : (T.walk i).toSubgraph=D.toSubgraph := hi.trans (C.toSubgraph_rotate hrC).symm
  have hDl : D.length=C.length := by
    have hh := congrArg Walk.length (C.take_spec hrC)
    simpa only [D,Walk.rotate,Walk.length_append,Nat.add_comm] using hh
  obtain ⟨u,v,hru,hvr,R,hform⟩ := cycle_two_spokes D hD
  have hCf : (Walk.cons hru (R.concat hvr)).IsCycle := hform ▸ hD
  have hif : (T.walk i).toSubgraph=(Walk.cons hru (R.concat hvr)).toSubgraph := by rw [←hform]; exact hDi
  have hRp : R.IsPath := ((Walk.cons_isCycle_iff _ _).mp hCf).1.of_append_left
  have huvne : u ≠ v := by
    intro he
    subst v
    have hnil := (Walk.isPath_iff_eq_nil R).mp hRp
    have hl := hCf.three_le_length
    simp only [hnil,Walk.length_cons,Walk.length_concat,Walk.length_nil] at hl
    omega
  obtain ⟨_,x,y,hxy,hN,hxyG⟩ := DegreeTwoReduction.degree_two_triangle hsmall hG hfail hr
  have hu : u=x ∨ u=y := (show u ∈ ({x,y} : Set (Fin n)) from hN ▸ hru)
  have hv : v=x ∨ v=y := (show v ∈ ({x,y} : Set (Fin n)) from hN ▸ hvr.symm)
  have huv : G.Adj u v := by
    rcases hu with rfl|rfl <;> rcases hv with rfl|rfl
    · exact (huvne rfl).elim
    · exact hxyG
    · exact hxyG.symm
    · exact (huvne rfl).elim
  obtain ⟨j,hj⟩ := (T.cover s(u,v)).mp huv
  have hji : j ≠ i := by
    intro he
    subst j
    rw [hif] at hj
    have hmem : s(u,v) ∈ R.edges := by
      have hh := (Walk.mem_edges_toSubgraph _).mp hj
      simp only [Walk.edges_cons,Walk.concat_eq_append,Walk.edges_append,Walk.edges_cons,
        Walk.edges_nil,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hh
      rcases hh with hh|hh|hh
      · have hh' := Sym2.eq_iff.mp hh
        rcases hh' with ⟨he,_⟩|⟨_,he⟩
        · exact (hru.ne he.symm).elim
        · exact (hvr.ne he).elim
      · exact hh
      · have hh' := Sym2.eq_iff.mp hh
        rcases hh' with ⟨he,_⟩|⟨he,_⟩
        · exact (huvne he).elim
        · exact (hru.ne he.symm).elim
    have hR := path_eq_singleton_of_endpoint_edge R hRp huv hmem
    have hetri : (T.walk i).toSubgraph=(Walk.cons hru (Walk.cons huv (Walk.cons hvr Walk.nil))).toSubgraph := by
      rw [hif,hR]; rfl
    exact TriangleAbsorption.budget_maximum_no_triangle T hG hs hm hk i hru huv hvr.symm hetri
  have hnp := cycle_member_not_path T i C hC hi
  have hjp := (T.one_defect_other_paths hs i hnp).2 j hji
  have hjn := NilSlot.max_score_nonpath_no_nil T hm ⟨i,hnp⟩ j
  have hjr := other_path_avoids_degree_two_cycle T i j hji.symm C hC hi hrC hr hjp hjn
  obtain ⟨U,E,hUs,hE,hUi,hlen⟩ := shorten_cycle_member T hs i j hji.symm hru hvr R hCf hif huv
    ((T.walk j).mem_edges_toSubgraph.mp hj) hjr
  have hbound := hmin U hUs i u E hE hUi
  rw [←hform,hDl] at hlen
  omega

lemma shortest_cycle_min_degree_three {n k : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (hk : Fintype.card (Fin n) ≤ 2*k)
    (i : Fin k) {a : Fin n} (C : G.Walk a a) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) (hmin : ShortestCycle T C.length)
    {r : Fin n} (hrC : r ∈ C.support) : 3 ≤ Nat.card (G.neighborSet r) := by
  have hb : 2 ≤ Nat.card (G.neighborSet r) := by
    rw [Nat.card_coe_set_eq,←hC.ncard_neighborSet_toSubgraph_eq_two hrC]
    exact Set.ncard_le_ncard (fun _ hh ↦ C.toSubgraph.adj_sub hh)
  have hn := shortest_cycle_no_degree_two hsmall hG hfail T hs hm hk i C hC hi hmin hrC
  by_contra hlt
  exact hn (by omega)

/-- If a whole cycle occurs at all, an equal-score family has a shortest
whole cycle whose vertices all have ambient degree at least three. -/
lemma exists_cycle_min_degree_three {n k : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (hk : Fintype.card (Fin n) ≤ 2*k)
    (i : Fin k) {a : Fin n} (C : G.Walk a a) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) :
    ∃ U : TrailFamily G k, ∃ j r, ∃ D : G.Walk r r,
      U.score=T.score ∧ D.IsCycle ∧ (U.walk j).toSubgraph=D.toSubgraph ∧
      ShortestCycle U D.length ∧ ∀ v ∈ D.support, 3 ≤ Nat.card (G.neighborSet v) := by
  obtain ⟨U,j,r,D,hUs,hD,hj,hmin⟩ := exists_shortest_cycle T i C hC hi
  refine ⟨U,j,r,D,hUs,hD,hj,hmin,?_⟩
  intro v hv
  apply shortest_cycle_min_degree_three hsmall hG hfail U (by omega)
    (fun W ↦ (hm W).trans (by omega)) hk j D hD hj hmin hv

end Erdos583CycleEarDevelopment
