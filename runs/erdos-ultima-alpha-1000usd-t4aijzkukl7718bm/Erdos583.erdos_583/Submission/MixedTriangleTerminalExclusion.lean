import Submission.TriangleTerminalSwitch

/-! The cubic nonroot vertex cannot be adjacent to the terminal vertex of the locked tail. -/
namespace Erdos583MixedTriangleTerminalExclusionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583TriangleTailRootTemplatesDevelopment Erdos583TriangleTerminalSwitchDevelopment
open Erdos583ShortTriangleIncidenceDevelopment Erdos583ShortTriangleSingleCarrierDevelopment
open Erdos583MixedTriangleTailLockDevelopment Erdos583ShortTriangleExternalCarrierDevelopment
open Erdos583ShortTriangleQuarticPairExclusionDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma path_cons_of_start_edge {V : Type*} {G : SimpleGraph V} {a b c : V}
    (P : G.Walk a b) (hp : P.IsPath) (h : G.Adj a c) (he : s(a,c) ∈ P.edges) :
    ∃ Q : G.Walk c b, P=Walk.cons h Q := by
  cases P with
  | nil => simp at he
  | @cons a x b g Q =>
    have heq : c=x := by simpa only [Walk.snd_cons] using hp.eq_snd_of_mem_edges he
    subst x
    exact ⟨Q,rfl⟩

lemma orient_path_at_endpoint {V : Type*} {G : SimpleGraph V} {a b y : V}
    (P : G.Walk a b) (hp : P.IsPath) (hy : y=a ∨ y=b) :
    ∃ d, ∃ Q : G.Walk y d, Q.IsPath ∧ P.toSubgraph=Q.toSubgraph := by
  rcases hy with hy | hy
  · exact ⟨b,P.copy hy.symm rfl,by simpa using hp,
      by simp only [NormalTrailSystem.walk_copy_subgraph]⟩
  · exact ⟨a,P.reverse.copy hy.symm rfl,by simpa using hp.reverse,
      by simp only [NormalTrailSystem.walk_copy_subgraph,Walk.toSubgraph_reverse]⟩

lemma frame_of_triangle_two_tail {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (L : RootedCycleRep T r) {x y s : V}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hC : L.cycle=Walk.cons hrx (Walk.cons hxy (Walk.cons hry.symm Walk.nil)))
    (hrs : G.Adj r s) (hst : G.Adj s L.finish)
    (hS : L.tail=Walk.cons hrs (Walk.cons hst Walk.nil)) :
    Nonempty (Frame G r x y s L.finish) := by
  have htr : L.finish ≠ r := by
    have hh := (Walk.cons_isPath_iff hrs _).mp (hS ▸ L.isPath) |>.2
    exact fun he ↦ hh (by simp [he])
  have hxS : x ∉ L.tail.support := fun hh ↦ hrx.ne.symm (L.inter x (by rw [hC]; simp) hh)
  have hyS : y ∉ L.tail.support := fun hh ↦ hry.ne.symm (L.inter y (by rw [hC]; simp) hh)
  have hsS : s ∈ L.tail.support := by rw [hS]; simp
  exact ⟨⟨hrx,hxy,hry,hrs,hst,htr,
    (fun he ↦ hxS (he ▸ hsS)),(fun he ↦ hyS (he ▸ hsS)),
    (fun he ↦ hxS (he ▸ L.tail.end_mem_support)),(fun he ↦ hyS (he ▸ L.tail.end_mem_support))⟩⟩

lemma failure_mixed_short_triangle_no_terminal_neighbor {n : ℕ}
    (hsmall : VertexCritical.SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (r : Fin n) (L : RootedCycleRep T r) {x y : Fin n}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hC : L.cycle=Walk.cons hrx (Walk.cons hxy (Walk.cons hry.symm Walk.nil)))
    (ht : L.tail.length=1 ∨ L.tail.length=2) (hd : Nat.card (G.neighborSet r)=5)
    (hdx : Nat.card (G.neighborSet x)=4) (hdy : Nat.card (G.neighborSet y)=3) :
    ¬G.Adj y L.finish := by
  intro hyt
  obtain ⟨hlen,a,b,c,hxa,hxb,_,_,har,hbr,_,_,_,_,_,habT,_⟩ :=
    failure_mixed_short_triangle_tail_lock hsmall hG hfail T hs hm r L hrx hxy hry hC ht hd hdx hdy
  obtain ⟨s,hrs,hst,hS⟩ := TriangleTailTwo.two_edge_form L.tail hlen
  obtain ⟨F⟩ := frame_of_triangle_two_tail T r L hrx hxy hry hC hrs hst hS
  have hstT : s(s,L.finish) ∈ L.tail.edges := by rw [hS]; simp
  have heab : s(a,b)=s(s,L.finish) := short_walk_noninitial_edges_eq L.tail (by omega) habT hstT
    (by simp [har.symm,hbr.symm]) (by simp [hrs.ne,F.tr.symm])
  have hxs : G.Adj x s := by
    rcases Sym2.eq_iff.mp heab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> assumption
  have hxt : G.Adj x L.finish := by
    rcases Sym2.eq_iff.mp heab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> assumption
  have hc : L.cycle.length=3 := by rw [hC]; rfl
  have hqr := (failure_any_short_triangle_root_degree hsmall hG hfail T hs hm r L hc (by omega)).1
  obtain ⟨j,hji,hrj,hunique⟩ := short_triangle_degree_five_unique_carrier T hs hm r L hc ht hqr hd
  have hyC : y ∈ L.cycle.support := by rw [hC]; simp
  have hxC : x ∈ L.cycle.support := by rw [hC]; simp
  obtain ⟨l,hli,hly⟩ := cubic_cycle_vertex_endpoint T r L hyC hry.ne.symm hdy
  have hyl : y ∈ (T.walk l).support := hly.elim
    (fun he ↦ he ▸ (T.walk l).start_mem_support) (fun he ↦ he ▸ (T.walk l).end_mem_support)
  have hlj := hunique l hli ⟨y,hyC,hyl⟩
  subst l
  obtain ⟨d,P,hP,hPe⟩ := orient_path_at_endpoint (T.walk j)
    ((T.one_defect_other_paths hs L.index L.member_not_path).2 j hji) hly
  have hedge {v z : Fin n} (hvC : v ∈ L.cycle.support) (hvr : v ≠ r) (hvz : G.Adj v z)
      (hzr : z ≠ r) (hzx : z ≠ x) (hzy : z ≠ y) : s(v,z) ∈ P.edges := by
    have hnot : s(v,z) ∉ L.cycle.toSubgraph.edgeSet := by
      rw [hC]
      simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false]
      simp [hzr,hzx,hzy]
    have he := unique_carrier_external_edge T r L j hunique hvC hvr hvz hnot
    rwa [←Walk.mem_edges_toSubgraph,hPe,Walk.mem_edges_toSubgraph] at he
  have hytP := hedge hyC hry.ne.symm hyt F.tr F.tx F.ty
  have hxtP := hedge hxC hrx.ne.symm hxt F.tr F.tx F.ty
  have hxsP := hedge hxC hrx.ne.symm hxs hrs.ne.symm F.sx F.sy
  obtain ⟨A,hPA⟩ := path_cons_of_start_edge P hP hyt hytP
  have hxtA : s(L.finish,x) ∈ A.edges := by
    rw [hPA,Walk.edges_cons,List.mem_cons] at hxtP
    rcases hxtP with he | he
    · have hh : x=y := by
        rcases Sym2.eq_iff.mp he with ⟨hx,_⟩ | ⟨hx,hy⟩
        · exact hx
        · exact (F.tx hx.symm).elim
      exact (hxy.ne hh).elim
    · simpa only [Sym2.eq_swap] using he
  obtain ⟨B,hAB⟩ := path_cons_of_start_edge A (hPA ▸ hP).of_cons hxt.symm hxtA
  have hxsB : s(x,s) ∈ B.edges := by
    rw [hPA,hAB,Walk.edges_cons,Walk.edges_cons,List.mem_cons,List.mem_cons] at hxsP
    rcases hxsP with he | he | he
    · rcases Sym2.eq_iff.mp he with ⟨hx,_⟩ | ⟨hx,_⟩
      · exact (hxy.ne hx).elim
      · exact (F.tx hx.symm).elim
    · rcases Sym2.eq_iff.mp he with ⟨hx,_⟩ | ⟨_,hx⟩
      · exact (F.tx hx.symm).elim
      · exact (F.st.ne hx).elim
    · exact he
  obtain ⟨R,hBR⟩ := path_cons_of_start_edge B (hAB ▸ (hPA ▸ hP).of_cons).of_cons hxs hxsB
  have hform : P=Walk.cons hyt (Walk.cons hxt.symm (Walk.cons hxs R)) := by rw [hPA,hAB,hBR]
  have hrP : r ∈ P.support := by rwa [←Walk.mem_verts_toSubgraph,hPe,Walk.mem_verts_toSubgraph] at hrj
  have hrR : r ∈ R.support := by
    simpa only [hform,Walk.support_cons,List.mem_cons,or_false,
      show r ≠ y from hry.ne,show r ≠ L.finish from F.tr.symm,show r ≠ x from hrx.ne,
      false_or] using hrP
  have hLe : (T.walk L.index).toSubgraph.edgeSet=F.edges := by
    rw [L.subgraph,hC,hS]
    ext e
    simp only [Frame.edges,Walk.mem_edges_toSubgraph,Walk.edges_append,Walk.edges_cons,
      Walk.edges_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
      Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := y) (b := r)]
    tauto
  exact failure_no_terminal_triangle_carrier hsmall hG hfail T hs hm L j hji.symm F
    hyt hxt.symm hxs R (hform ▸ hP) hLe (hPe.trans (congrArg Walk.toSubgraph hform)) hrR hd hdx

end Erdos583MixedTriangleTerminalExclusionDevelopment
