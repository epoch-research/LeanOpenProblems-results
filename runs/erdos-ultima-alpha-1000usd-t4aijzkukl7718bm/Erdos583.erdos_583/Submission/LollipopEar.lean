import Submission.Work

/-! An ear exchange preserves an attached tail and all family endpoint quotas. -/
namespace Erdos583LollipopEarDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open scoped Classical
set_option maxHeartbeats 1800000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
lemma edge_disjoint_of_one_common_vertex {a b c d r : V}
    (P : G.Walk a b) (Q : G.Walk c d)
    (hinter : ∀ z ∈ P.support, z ∈ Q.support → z=r) :
    Disjoint P.toSubgraph.edgeSet Q.toSubgraph.edgeSet := by
  apply Set.disjoint_left.mpr
  intro e heP heQ
  induction e using Sym2.ind with
  | h u v =>
    have hu := hinter u (P.fst_mem_support_of_mem_edges (P.mem_edges_toSubgraph.mp heP))
      (Q.fst_mem_support_of_mem_edges (Q.mem_edges_toSubgraph.mp heQ))
    have hv := hinter v (P.snd_mem_support_of_mem_edges (P.mem_edges_toSubgraph.mp heP))
      (Q.snd_mem_support_of_mem_edges (Q.mem_edges_toSubgraph.mp heQ))
    exact (P.toSubgraph.adj_sub heP).ne (hu.trans hv.symm)

lemma lollipop_vertex_card {r b : V} (C : G.Walk r r) (hc : C.IsCycle)
    (S : G.Walk r b) (hs : S.IsPath)
    (hinter : ∀ z ∈ C.support, z ∈ S.support → z=r) :
    (C.append S).toSubgraph.verts.ncard=(C.append S).length := by
  have hI : C.toSubgraph.verts ∩ S.toSubgraph.verts={r} := by
    ext z
    constructor
    · intro hz
      exact hinter z (by simpa only [Walk.mem_verts_toSubgraph] using hz.1)
        (by simpa only [Walk.mem_verts_toSubgraph] using hz.2)
    · rintro rfl
      exact ⟨C.start_mem_verts_toSubgraph,S.start_mem_verts_toSubgraph⟩
  have hCv : C.toSubgraph.verts.ncard=C.length := by
    rw [Walk.verts_toSubgraph,cycle_support_ncard hc]
  have hh := Set.ncard_union_add_ncard_inter C.toSubgraph.verts S.toSubgraph.verts
  rw [hI,Set.ncard_singleton,hCv,(walk_vertex_ncard_eq_iff S).mpr hs] at hh
  simp only [Walk.toSubgraph_append,Subgraph.verts_sup,Walk.length_append]
  omega

/-- The cycle is based at the removed ear vertex x, while the retained
attached tail starts at another cycle vertex r. The exchange shortens the
cycle, leaves the tail unchanged, and does not change the other path's ends. -/
lemma ear_exchange_with_tail {a b d x u v r : V}
    (hxu : G.Adj x u) (hvx : G.Adj v x) (R : G.Walk u v)
    (hc : (Walk.cons hxu (R.concat hvx)).IsCycle) (hr : r ∈ R.support)
    (S : G.Walk r b) (hS : S.IsPath)
    (hinter : ∀ z ∈ (Walk.cons hxu (R.concat hvx)).support, z ∈ S.support → z=r)
    (P : G.Walk a d) (hP : P.IsPath) (huv : G.Adj u v)
    (he : s(u,v) ∈ P.edges) (hxP : x ∉ P.support)
    (hd : Disjoint ((Walk.cons hxu (R.concat hvx)).toSubgraph.edgeSet ∪ S.toSubgraph.edgeSet)
      P.toSubgraph.edgeSet) :
    ∃ E : G.Walk r r, ∃ Q : G.Walk a d,
      E.IsCycle ∧ Q.IsPath ∧ E.length+1=(Walk.cons hxu (R.concat hvx)).length ∧
      E.toSubgraph.verts ⊆ (Walk.cons hxu (R.concat hvx)).toSubgraph.verts ∧
      (∀ z ∈ E.support, z ∈ S.support → z=r) ∧ (E.append S).IsTrail ∧
      Disjoint (E.append S).toSubgraph.edgeSet Q.toSubgraph.edgeSet ∧
      (E.append S).toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet =
        ((Walk.cons hxu (R.concat hvx)).toSubgraph.edgeSet ∪ S.toSubgraph.edgeSet) ∪ P.toSubgraph.edgeSet := by
  classical
  let C := Walk.cons hxu (R.concat hvx)
  obtain ⟨hD,Q,hQ,hsep,hcover,hlen⟩ := CycleEar.cycle_ear_exchange hxu hvx R hc P hP huv he hxP
    (disjoint_sup_left.mp hd).1
  let D := Walk.cons huv R.reverse
  have hrD : r ∈ D.support := by
    simp only [D,Walk.support_cons,Walk.support_reverse,List.mem_cons,List.mem_reverse]
    exact Or.inr hr
  let E := D.rotate hrD
  have hE : E.IsCycle := hD.rotate hrD
  have hED : E.toSubgraph=D.toSubgraph := D.toSubgraph_rotate hrD
  have hElen : E.length=D.length := by
    rw [←trail_edgeSet_ncard E hE.isTrail,hED,trail_edgeSet_ncard D hD.isTrail]
  have hsub : E.toSubgraph.verts ⊆ C.toSubgraph.verts := by
    intro z hz
    rw [hED,Walk.mem_verts_toSubgraph] at hz
    have hzR : z ∈ R.support := by
      rcases (show z=u ∨ z ∈ R.support by
        simpa only [D,Walk.support_cons,Walk.support_reverse,List.mem_cons,List.mem_reverse] using hz) with rfl|hzR
      · exact R.start_mem_support
      · exact hzR
    simp only [C,Walk.mem_verts_toSubgraph,Walk.support_cons,Walk.support_concat,
      List.mem_cons,List.concat_eq_append,List.mem_append]
    exact Or.inr (Or.inl hzR)
  have hint : ∀ z ∈ E.support, z ∈ S.support → z=r := by
    intro z hzE hzS
    apply hinter z _ hzS
    have hz := hsub (E.mem_verts_toSubgraph.mpr hzE)
    simpa only [Walk.mem_verts_toSubgraph] using hz
  have hES := edge_disjoint_of_one_common_vertex E S hint
  have hCS := edge_disjoint_of_one_common_vertex C S hinter
  have hQS : Disjoint Q.toSubgraph.edgeSet S.toSubgraph.edgeSet := by
    apply (disjoint_sup_left.mpr ⟨hCS,(disjoint_sup_left.mp hd).2.symm⟩).mono_left
    intro e heQ
    change e ∈ (Walk.cons hxu (R.concat hvx)).toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet
    rw [←hcover]
    exact Or.inr heQ
  have hEQ : Disjoint E.toSubgraph.edgeSet Q.toSubgraph.edgeSet := by rw [hED]; exact hsep
  have hsep' : Disjoint (E.append S).toSubgraph.edgeSet Q.toSubgraph.edgeSet := by
    rw [Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    exact disjoint_sup_left.mpr ⟨hEQ,hQS.symm⟩
  have hcover' : (E.append S).toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet =
      (C.toSubgraph.edgeSet ∪ S.toSubgraph.edgeSet) ∪ P.toSubgraph.edgeSet := by
    rw [Walk.toSubgraph_append,Subgraph.edgeSet_sup,hED]
    have hh := hcover
    change D.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet=C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet at hh
    rw [show (D.toSubgraph.edgeSet ∪ S.toSubgraph.edgeSet) ∪ Q.toSubgraph.edgeSet =
      (D.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet) ∪ S.toSubgraph.edgeSet by ext e; simp only [Set.mem_union]; tauto,
      hh]
    ext e
    simp only [Set.mem_union]
    tauto
  exact ⟨E,Q,hE,hQ,by rw [hElen]; exact hlen,hsub,hint,trail_append_of_disjoint hE.isTrail hS.isTrail hES,hsep',hcover'⟩

/-- A missing ear can be moved from a rooted member's cycle into another
path without changing the score, the root, or any endpoint quota. The root
itself lies on the retained part R and is not the removed ear vertex. -/
lemma shorten_rooted_member {k : ℕ} (T : TrailFamily G k) (i j : Fin k) (hij : i ≠ j)
    (C : G.Walk (T.start i) (T.start i)) (hc : C.IsCycle)
    (S : G.Walk (T.start i) (T.finish i)) (hS : S.IsPath)
    (hinter : ∀ z ∈ C.support, z ∈ S.support → z=T.start i)
    (hi : (T.walk i).toSubgraph=(C.append S).toSubgraph)
    {x u v : V} (hxu : G.Adj x u) (hvx : G.Adj v x) (R : G.Walk u v)
    (hD : (Walk.cons hxu (R.concat hvx)).IsCycle)
    (hDC : (Walk.cons hxu (R.concat hvx)).toSubgraph=C.toSubgraph)
    (hr : T.start i ∈ R.support)
    (hj : (T.walk j).IsPath) (huv : G.Adj u v)
    (he : s(u,v) ∈ (T.walk j).edges) (hx : x ∉ (T.walk j).support) :
    ∃ U : TrailFamily G k, ∃ E : G.Walk (T.start i) (T.start i),
      U.score=T.score ∧ (∀ z, U.quota z=T.quota z) ∧ HasRoot U (T.start i) ∧
      U.start i=T.start i ∧ U.finish i=T.finish i ∧ E.IsCycle ∧ E.length+1=C.length ∧
      (U.walk i).toSubgraph=(E.append S).toSubgraph ∧
      (∀ z ∈ E.support, z ∈ S.support → z=T.start i) := by
  classical
  have hd : Disjoint ((Walk.cons hxu (R.concat hvx)).toSubgraph.edgeSet ∪ S.toSubgraph.edgeSet)
      (T.walk j).toSubgraph.edgeSet := by
    rw [hDC,←Subgraph.edgeSet_sup,←Walk.toSubgraph_append,←hi]
    exact T.disjoint hij
  have hintD (z : V) (hzD : z ∈ (Walk.cons hxu (R.concat hvx)).support)
      (hzS : z ∈ S.support) : z=T.start i := by
    apply hinter z _ hzS
    rwa [←Walk.mem_verts_toSubgraph,hDC,Walk.mem_verts_toSubgraph] at hzD
  obtain ⟨E,Q,hE,hQ,hlen,hsub,hint,htrail,hsep,hcover⟩ :=
    ear_exchange_with_tail hxu hvx R hD hr S hS hintD (T.walk j) hj huv he hx hd
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
  have hDl : (Walk.cons hxu (R.concat hvx)).length=C.length := by
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
  refine ⟨U,E,by omega,?_,hUroot,hUa,hUb,hE,hlen.trans hDl,hUi,hint⟩
  intro z
  have hh := hquota z
  omega

/-- A cycle followed by a simple tail meeting it only at the root. Unlike
HasRoot, this data fixes an orientation of the indexed member. -/
structure RootedCycleRep {k : ℕ} (T : TrailFamily G k) (r : V) where
  index : Fin k
  finish : V
  start_eq : T.start index=r
  finish_eq : T.finish index=finish
  cycle : G.Walk r r
  tail : G.Walk r finish
  isCycle : cycle.IsCycle
  isPath : tail.IsPath
  inter : ∀ z ∈ cycle.support, z ∈ tail.support → z=r
  subgraph : (T.walk index).toSubgraph=(cycle.append tail).toSubgraph

omit [Fintype V] in
lemma RootedCycleRep.hasRoot {k : ℕ} {T : TrailFamily G k} {r : V}
    (L : RootedCycleRep T r) : HasRoot T r := by
  have hd := edge_disjoint_of_one_common_vertex L.cycle L.tail L.inter
  exact ThreeTransfer.hasRoot_of_append_rep T L.index L.start_eq L.finish_eq
    L.cycle L.tail L.isCycle.not_nil
    (trail_append_of_disjoint L.isCycle.isTrail L.isPath.isTrail hd)
    L.tail.start_mem_support L.subgraph

/-- A single rooted defect admits an oriented cycle-and-tail representation
without changing its score, any indexed subgraph, or any endpoint quota. -/
lemma exists_rooted_cycle_rep {k : ℕ} (T : TrailFamily G k) (r : V)
    (hs : T.score+1=G.edgeSet.ncard+k) (hroot : HasRoot T r) :
    ∃ U : TrailFamily G k, U.score=T.score ∧ (∀ z, U.quota z=T.quota z) ∧
      (∀ i, (U.walk i).toSubgraph=(T.walk i).toSubgraph) ∧ Nonempty (RootedCycleRep U r) := by
  classical
  obtain ⟨A,B,ρ,hρ,hn⟩ := hroot
  have hx : (B.tail ρ).toSubgraph.Adj r (B.tail ρ).snd := by
    simpa only [hρ] using (B.tail ρ).toSubgraph_adj_snd hn
  obtain ⟨i,b,h,p,_,hends,ht,he,hrep⟩ := rooted_exposed_rep B ρ hρ hx
  obtain ⟨hp,_,_⟩ := simple_tail_of_one_defect_rep T hs i h p ht he hrep
  let C := Walk.cons h (p.takeUntil r hrep)
  let S := p.dropUntil r hrep
  have hC : C.IsCycle := (Walk.cons_isCycle_iff _ h).mpr
    ⟨hp.takeUntil hrep,fun hm ↦ (Walk.isTrail_cons h p).mp ht |>.2 (p.edges_takeUntil_subset hrep hm)⟩
  have hS : S.IsPath := hp.dropUntil hrep
  have hform : C.append S=Walk.cons h p := by
    simp only [C,S,Walk.cons_append,Walk.take_spec]
  have hCS : (C.append S).IsTrail := hform.symm ▸ ht
  have hint (z : V) (hzC : z ∈ C.support) (hzS : z ∈ S.support) : z=r := by
    rcases (show z=r ∨ z ∈ (p.takeUntil r hrep).support by
      simpa only [C,Walk.support_cons,List.mem_cons] using hzC) with hz|hz
    · exact hz
    · have hpath : ((p.takeUntil r hrep).append (p.dropUntil r hrep)).IsPath := by
        simpa only [Walk.take_spec] using hp
      by_contra hzr
      exact (hpath.ne_of_mem_support_of_append hzr hz hzS) rfl
  have he' : (C.append S).toSubgraph=(T.walk i).toSubgraph := by rw [hform]; exact he.symm
  obtain ⟨U,hUs,ha,hb,hparts,hq⟩ := replace_one_general T i (C.append S) hCS he'
  have hUq (z : V) : U.quota z=T.quota z := by
    have hh := hq z
    rcases hends with ⟨hstart,hfinish⟩|⟨hfinish,hstart⟩
    · rw [hstart,hfinish] at hh
      omega
    · rw [hstart,hfinish] at hh
      omega
  exact ⟨U,hUs,hUq,hparts,⟨⟨i,b,ha,hb,C,S,hC,hS,hint,(hparts i).trans he'.symm⟩⟩⟩

/-- Minimize cycle length while fixing the root, every endpoint quota, and
the incidence score. This minimum does not require rootifying an internal
repetition: its feasible set consists only of explicit rooted witnesses. -/
lemma exists_shortest_rooted_cycle {k : ℕ} (T : TrailFamily G k) (r : V)
    (hs : T.score+1=G.edgeSet.ncard+k) (hroot : HasRoot T r) :
    ∃ U : TrailFamily G k, ∃ L : RootedCycleRep U r,
      U.score=T.score ∧ (∀ z, U.quota z=T.quota z) ∧
      ∀ W : TrailFamily G k, ∀ M : RootedCycleRep W r,
        W.score=T.score → (∀ z, W.quota z=T.quota z) → L.cycle.length ≤ M.cycle.length := by
  classical
  let P (m : ℕ) := ∃ U : TrailFamily G k, ∃ L : RootedCycleRep U r,
    U.score=T.score ∧ (∀ z, U.quota z=T.quota z) ∧ L.cycle.length=m
  obtain ⟨S,hSs,hSq,_,⟨L⟩⟩ := exists_rooted_cycle_rep T r hs hroot
  have hex : ∃ m, P m := ⟨L.cycle.length,S,L,hSs,hSq,rfl⟩
  obtain ⟨U,M,hUs,hUq,hl⟩ := Nat.find_spec hex
  refine ⟨U,M,hUs,hUq,?_⟩
  intro W N hWs hWq
  rw [hl]
  exact Nat.find_min' hex ⟨W,N,hWs,hWq,rfl⟩

lemma RootedCycleRep.member_not_path {k : ℕ} {T : TrailFamily G k} {r : V}
    (L : RootedCycleRep T r) : ¬(T.walk L.index).IsPath := by
  intro hp
  have ht := trail_append_of_disjoint L.isCycle.isTrail L.isPath.isTrail
    (edge_disjoint_of_one_common_vertex L.cycle L.tail L.inter)
  have hl : (T.walk L.index).length=(L.cycle.append L.tail).length := by
    rw [←trail_edgeSet_ncard _ (T.isTrail L.index),L.subgraph,trail_edgeSet_ncard _ ht]
  have hh := (walk_vertex_ncard_eq_iff _).mpr hp
  rw [L.subgraph,lollipop_vertex_card L.cycle L.isCycle L.tail L.isPath L.inter,hl] at hh
  omega

lemma RootedCycleRep.no_removable_ear {k : ℕ} (T : TrailFamily G k) (r : V)
    (L : RootedCycleRep T r)
    (hmin : ∀ W : TrailFamily G k, ∀ M : RootedCycleRep W r,
      W.score=T.score → (∀ z, W.quota z=T.quota z) → L.cycle.length ≤ M.cycle.length)
    (j : Fin k) (hij : L.index ≠ j) {x u v : V}
    (hxu : G.Adj x u) (hvx : G.Adj v x) (R : G.Walk u v)
    (hD : (Walk.cons hxu (R.concat hvx)).IsCycle)
    (hDC : (Walk.cons hxu (R.concat hvx)).toSubgraph=L.cycle.toSubgraph)
    (hr : r ∈ R.support) (hj : (T.walk j).IsPath) (huv : G.Adj u v)
    (he : s(u,v) ∈ (T.walk j).edges) (hx : x ∉ (T.walk j).support) : False := by
  rcases L with ⟨i,b,ha,hb,C,S,hC,hS,hinter,hsub⟩
  dsimp only at *
  subst r b
  obtain ⟨U,E,hUs,hUq,hUr,hUa,hUb,hE,hEl,hUi,hint⟩ :=
    shorten_rooted_member T i j hij C hC S hS hinter hsub hxu hvx R hD hDC hr hj huv he hx
  let M : RootedCycleRep U (T.start i) := ⟨i,T.finish i,hUa,hUb,E,S,hE,hS,hint,hUi⟩
  have hh := hmin U M hUs hUq
  change C.length ≤ E.length at hh
  omega

lemma degree_two_cycle_other_avoids {k : ℕ} (T : TrailFamily G k) (i j : Fin k) (hij : i ≠ j)
    {a x : V} (C : G.Walk a a) (hc : C.IsCycle)
    (hi : C.toSubgraph.edgeSet ⊆ (T.walk i).toSubgraph.edgeSet)
    (hxC : x ∈ C.support) (hd : Nat.card (G.neighborSet x)=2)
    (hj : (T.walk j).IsPath) (hn : ¬(T.walk j).Nil) : x ∉ (T.walk j).support := by
  have hN : C.toSubgraph.neighborSet x=G.neighborSet x := by
    apply Set.eq_of_subset_of_ncard_le (fun _ hh ↦ C.toSubgraph.adj_sub hh)
    change (G.neighborSet x).ncard ≤ (C.toSubgraph.neighborSet x).ncard
    rw [hc.ncard_neighborSet_toSubgraph_eq_two hxC,←Nat.card_coe_set_eq,hd]
  intro hxj
  obtain ⟨z,hz⟩ := (Set.ncard_pos (Set.toFinite _)).mp (path_neighbor_ncard_pos hj hn hxj)
  have hxz : C.toSubgraph.Adj x z := by
    change z ∈ C.toSubgraph.neighborSet x
    rw [hN]
    exact (T.walk j).toSubgraph.adj_sub hz
  exact Set.disjoint_left.mp (T.disjoint hij)
    (hi (show s(x,z) ∈ C.toSubgraph.edgeSet from hxz))
    (show s(x,z) ∈ (T.walk j).toSubgraph.edgeSet from hz)

/-- In a smallest failure, a shortest rooted cycle of length at least four
has no degree-two vertex, provided the fixed root has degree at least three.
The triangle alternative is deliberately not excluded. -/
lemma shortest_rooted_cycle_no_degree_two {n k : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G k) (r : Fin n) (L : RootedCycleRep T r)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hmin : ∀ W : TrailFamily G k, ∀ M : RootedCycleRep W r,
      W.score=T.score → (∀ z, W.quota z=T.quota z) → L.cycle.length ≤ M.cycle.length)
    (hdeg : 3 ≤ Nat.card (G.neighborSet r)) (hlen : 4 ≤ L.cycle.length)
    {x : Fin n} (hxC : x ∈ L.cycle.support) (hx : Nat.card (G.neighborSet x)=2) : False := by
  classical
  have hrx : r ≠ x := by rintro rfl; omega
  let D := L.cycle.rotate hxC
  have hD : D.IsCycle := L.isCycle.rotate hxC
  have hDC : D.toSubgraph=L.cycle.toSubgraph := L.cycle.toSubgraph_rotate hxC
  have hDl : D.length=L.cycle.length := by
    rw [←trail_edgeSet_ncard D hD.isTrail,hDC,trail_edgeSet_ncard _ L.isCycle.isTrail]
  obtain ⟨u,v,hxu,hvx,R,hform⟩ := CycleEar.cycle_two_spokes D hD
  have hDf := hform ▸ hD
  have hR := (Walk.cons_isCycle_iff _ hxu).mp hDf |>.1.of_append_left
  have hRlen : 2 ≤ R.length := by
    rw [hform] at hDl
    simp only [Walk.length_cons,Walk.length_concat] at hDl
    omega
  have huvne : u ≠ v := by
    intro hh
    subst v
    have hh' := (Walk.isPath_iff_eq_nil R).mp hR
    simp [hh'] at hRlen
  have hmem (z : Fin n) : z ∈ R.support → z ∈ L.cycle.support := by
    intro hz
    rw [←Walk.mem_verts_toSubgraph,←hDC,hform,Walk.mem_verts_toSubgraph]
    simp only [Walk.support_cons,Walk.support_concat,List.mem_cons,List.concat_eq_append,List.mem_append]
    exact Or.inr (Or.inl hz)
  have hrR : r ∈ R.support := by
    have hrD : r ∈ D.support := by
      rw [←Walk.mem_verts_toSubgraph,hDC,Walk.mem_verts_toSubgraph]
      exact L.cycle.start_mem_support
    simpa only [hform,Walk.support_cons,Walk.support_concat,List.mem_cons,List.concat_eq_append,
      List.mem_append,List.not_mem_nil,hrx,false_or,or_false] using hrD
  obtain ⟨_,s,t,hst,hN,hstG⟩ := DegreeTwoReduction.degree_two_triangle hsmall hG hfail hx
  have hu : u=s ∨ u=t := (show u ∈ ({s,t} : Set (Fin n)) from hN ▸ hxu)
  have hv : v=s ∨ v=t := (show v ∈ ({s,t} : Set (Fin n)) from hN ▸ hvx.symm)
  have huv : G.Adj u v := by
    rcases hu with rfl|rfl <;> rcases hv with rfl|rfl
    · exact (huvne rfl).elim
    · exact hstG
    · exact hstG.symm
    · exact (huvne rfl).elim
  have heR : s(u,v) ∉ R.edges := by
    intro he
    have hh := PentagonIntersection.endpoint_edge_forces_length_one R hR he
    omega
  have heD : s(u,v) ∉ D.edges := by
    rw [hform]
    simp only [Walk.edges_cons,Walk.edges_concat,List.mem_cons,List.concat_eq_append,
      List.mem_append,List.not_mem_nil,or_false,not_or]
    refine ⟨?_,heR,?_⟩
    · intro hh
      rcases Sym2.eq_iff.mp hh with ⟨hux,_⟩|⟨_,hvx'⟩
      · exact hxu.ne hux.symm
      · exact hvx.ne hvx'
    · intro hh
      rcases Sym2.eq_iff.mp hh with ⟨huv',_⟩|⟨hux,_⟩
      · exact huvne huv'
      · exact hxu.ne hux.symm
  obtain ⟨j,hj⟩ := (T.cover s(u,v)).mp huv
  have hji : j ≠ L.index := by
    intro hh
    subst j
    rw [L.subgraph,Walk.toSubgraph_append,Subgraph.edgeSet_sup] at hj
    rcases hj with hj|hj
    · exact heD (D.mem_edges_toSubgraph.mp (hDC.symm ▸ hj))
    · have huS := L.tail.fst_mem_support_of_mem_edges (L.tail.mem_edges_toSubgraph.mp hj)
      have hvS := L.tail.snd_mem_support_of_mem_edges (L.tail.mem_edges_toSubgraph.mp hj)
      exact huvne ((L.inter u (hmem u R.start_mem_support) huS).trans
        (L.inter v (hmem v R.end_mem_support) hvS).symm)
  have hnp := L.member_not_path
  have hjp := (T.one_defect_other_paths hs L.index hnp).2 j hji
  have hjn := NilSlot.max_score_nonpath_no_nil T hm ⟨L.index,hnp⟩ j
  have hsubset : L.cycle.toSubgraph.edgeSet ⊆ (T.walk L.index).toSubgraph.edgeSet := by
    rw [L.subgraph,Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    exact Set.subset_union_left
  have hxj := degree_two_cycle_other_avoids T L.index j hji.symm L.cycle L.isCycle hsubset hxC hx hjp hjn
  exact L.no_removable_ear T r hmin j hji.symm hxu hvx R hDf
    (by rw [←hform]; exact hDC) hrR hjp huv ((T.walk j).mem_edges_toSubgraph.mp hj) hxj

/-- At fixed root and fixed quotas, select a shortest lollipop cycle. It
is either a triangle or all of its vertices have ambient degree at least
three. This includes open lollipops, but does not rule out the triangle case. -/
lemma exists_shortest_rooted_cycle_structure {n k : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G k) (r : Fin n) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (hroot : HasRoot T r)
    (hdeg : 3 ≤ Nat.card (G.neighborSet r)) :
    ∃ U : TrailFamily G k, ∃ L : RootedCycleRep U r,
      U.score=T.score ∧ (∀ z, U.quota z=T.quota z) ∧
      RootEnergy.quotaEnergy U=RootEnergy.quotaEnergy T ∧ HasRoot U r ∧
      (L.cycle.length=3 ∨ ∀ x ∈ L.cycle.support, 3 ≤ Nat.card (G.neighborSet x)) ∧
      ∀ W : TrailFamily G k, ∀ M : RootedCycleRep W r,
        W.score=U.score → (∀ z, W.quota z=U.quota z) → L.cycle.length ≤ M.cycle.length := by
  obtain ⟨U,L,hUs,hUq,hmin⟩ := exists_shortest_rooted_cycle T r hs hroot
  have hminU (W : TrailFamily G k) (M : RootedCycleRep W r) (hWs : W.score=U.score)
      (hWq : ∀ z, W.quota z=U.quota z) : L.cycle.length ≤ M.cycle.length :=
    hmin W M (hWs.trans hUs) (fun z ↦ (hWq z).trans (hUq z))
  have henergy : RootEnergy.quotaEnergy U=RootEnergy.quotaEnergy T := by
    apply Finset.sum_congr rfl
    intro z _
    rw [hUq]
  refine ⟨U,L,hUs,hUq,henergy,L.hasRoot,?_,hminU⟩
  by_cases h3 : L.cycle.length=3
  · exact Or.inl h3
  · right
    intro x hxC
    have hc3 := L.isCycle.three_le_length
    have h2 : 2 ≤ Nat.card (G.neighborSet x) := by
      rw [Nat.card_coe_set_eq,←L.isCycle.ncard_neighborSet_toSubgraph_eq_two hxC]
      exact Set.ncard_le_ncard (fun _ hh ↦ L.cycle.toSubgraph.adj_sub hh)
    have hn := shortest_rooted_cycle_no_degree_two hsmall hG hfail U r L (by omega)
      (fun W ↦ (hm W).trans (by omega)) hminU hdeg (by omega) hxC
    by_contra hlt
    exact hn (by omega)

end Erdos583LollipopEarDevelopment
