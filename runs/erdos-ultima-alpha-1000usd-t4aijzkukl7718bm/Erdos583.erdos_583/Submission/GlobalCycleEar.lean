import Submission.GlobalTailExchange
import Submission.TailPrefixRunFreshness

/-! Exchanges using a whole normal member as an ear of the root cycle. -/
namespace Erdos583GlobalCycleEarDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583GeneralPairEndpointsDevelopment Erdos583GlobalTailDefectDevelopment
open Erdos583UnifiedMinimalDefectDevelopment Erdos583TailPrefixRunFreshnessDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma cycle_of_two_paths {V : Type*} {G : SimpleGraph V} {s t : V}
    (P B : G.Walk s t) (hp : P.IsPath) (hb : B.IsPath) (hst : s ≠ t)
    (hd : Disjoint P.toSubgraph.edgeSet B.toSubgraph.edgeSet)
    (hi : ∀ x ∈ P.support, x ∈ B.support → x=s ∨ x=t) :
    (P.append B.reverse).IsCycle := by
  cases P with
  | nil => exact (hst rfl).elim
  | @cons s a t h Q =>
    obtain ⟨hQ,hsQ⟩ := (Walk.cons_isPath_iff h Q).mp hp
    have hQB : (Q.append B.reverse).IsPath := by
      apply path_append_of_support_intersection hQ hb.reverse
      intro x hxQ hxB
      have hx := hi x (List.mem_cons_of_mem _ hxQ) (by simpa using hxB)
      exact hx.resolve_left (fun he ↦ hsQ (he ▸ hxQ))
    rw [Walk.cons_append,Walk.cons_isCycle_iff]
    refine ⟨hQB,?_⟩
    rw [Walk.edges_append]
    intro he
    rcases List.mem_append.mp he with he|he
    · exact (List.nodup_cons.mp hp.isTrail.edges_nodup).1 he
    · have heP : s(s,a) ∈ (Walk.cons h Q).toSubgraph.edgeSet :=
        (Walk.cons h Q).mem_edges_toSubgraph.mpr (by simp)
      have heB : s(s,a) ∈ B.toSubgraph.edgeSet :=
        B.mem_edges_toSubgraph.mpr (by simpa using he)
      exact Set.disjoint_left.mp hd heP heB

/-- Three nonempty consecutive arcs of a cycle, and a whole path-member
joining the two nonroot cuts, produce a new rooted lollipop. The old tail
may intersect the ear; it belongs to the new ordinary path instead. -/
lemma exchange_cycle_ear {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (L : RootedCycleRep T r)
    (j : Fin k) (hij : L.index ≠ j) {s t : V}
    (A : G.Walk r s) (B : G.Walk s t) (E : G.Walk t r)
    (hrs : r ≠ s) (hst : s ≠ t) (htr : t ≠ r)
    (hform : L.cycle=(A.append B).append E)
    (P : G.Walk s t) (hp : P.IsPath) (hP : (T.walk j).toSubgraph=P.toSubgraph)
    (hinter : ∀ x ∈ P.support, x ∈ L.cycle.support → x=s ∨ x=t) :
    ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U s,
      U.score=T.score ∧ M.cycle.length=P.length+B.length ∧
      M.tail.length=A.length ∧
      (U.walk j).toSubgraph=(E.append L.tail).toSubgraph ∧
      ∀ i, i ≠ L.index → i ≠ j → (U.walk i).toSubgraph=(T.walk i).toSubgraph := by
  have hC : ((A.append B).append E).IsCycle := hform ▸ L.isCycle
  have hAB := hC.isPath_of_append_left (Walk.not_nil_of_ne htr)
  have hBE : (B.append E).IsPath := by
    apply Walk.IsCycle.isPath_of_append_right (Walk.not_nil_of_ne hrs)
    simpa only [Walk.append_assoc] using hC
  have hEA : (E.append A).IsPath := by
    apply Walk.IsCycle.isPath_of_append_left (Walk.not_nil_of_ne hst)
    have hh := isCycle_append_comm hC
    simpa only [Walk.append_assoc] using hh
  have hAC (x : V) (hx : x ∈ A.support) : x ∈ L.cycle.support := by
    rw [hform,Walk.mem_support_append_iff,Walk.mem_support_append_iff]
    exact Or.inl (Or.inl hx)
  have hBC (x : V) (hx : x ∈ B.support) : x ∈ L.cycle.support := by
    rw [hform,Walk.mem_support_append_iff,Walk.mem_support_append_iff]
    exact Or.inl (Or.inr hx)
  have hEC (x : V) (hx : x ∈ E.support) : x ∈ L.cycle.support := by
    rw [hform,Walk.mem_support_append_iff]
    exact Or.inr hx
  have hPB : Disjoint P.toSubgraph.edgeSet B.toSubgraph.edgeSet := by
    apply (T.disjoint hij.symm).mono
    · rw [hP]
    · rw [L.subgraph,hform]
      simp only [Walk.toSubgraph_append,Subgraph.edgeSet_sup]
      intro e he
      exact Or.inl (Or.inl (Or.inr he))
  let C := P.append B.reverse
  have hnewC : C.IsCycle := cycle_of_two_paths P B hp hAB.of_append_right hst hPB
    (fun x hxP hxB ↦ hinter x hxP (hBC x hxB))
  have hCA (x : V) (hxC : x ∈ C.support) (hxA : x ∈ A.reverse.support) : x=s := by
    have hxA' : x ∈ A.support := by simpa using hxA
    change x ∈ (P.append B.reverse).support at hxC
    rw [Walk.mem_support_append_iff] at hxC
    rcases hxC with hxP|hxB
    · rcases hinter x hxP (hAC x hxA') with hxs|hxt
      · exact hxs
      · have hh := path_append_support_inter A B hAB hxA' (hxt ▸ B.end_mem_support)
        exact (hst (hh.symm.trans hxt)).elim
    · exact path_append_support_inter A B hAB hxA' (by simpa using hxB)
  have hET : (E.append L.tail).IsPath := by
    apply path_append_of_support_intersection hBE.of_append_right L.isPath
    exact fun x hxE hxT ↦ L.inter x (hEC x hxE) hxT
  have hnew : (C.append A.reverse).IsTrail := trail_append_of_disjoint hnewC.isTrail
    hAB.of_append_left.reverse.isTrail (edge_disjoint_of_one_common_vertex C A.reverse hCA)
  have hc : (C.append A.reverse).toSubgraph.edgeSet ∪ (E.append L.tail).toSubgraph.edgeSet=
      (T.walk L.index).toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet := by
    rw [L.subgraph,hP,hform]
    simp only [C,Walk.toSubgraph_append,Walk.toSubgraph_reverse,Subgraph.edgeSet_sup]
    ext e
    simp only [Set.mem_union]
    tauto
  have hlen : (C.append A.reverse).length+(E.append L.tail).length=
      ((T.walk L.index).toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet).ncard := by
    rw [Set.ncard_union_eq (T.disjoint hij),trail_edgeSet_ncard _ (T.isTrail L.index)]
    have hLi : (T.walk L.index).length=L.cycle.length+L.tail.length := by
      rw [←trail_edgeSet_ncard _ (T.isTrail L.index),L.subgraph,
        trail_edgeSet_ncard _ (trail_append_of_disjoint L.isCycle.isTrail L.isPath.isTrail
          (edge_disjoint_of_one_common_vertex L.cycle L.tail L.inter)),Walk.length_append]
    rw [hLi,hP,trail_edgeSet_ncard P hp.isTrail,hform]
    simp only [C,Walk.length_append,Walk.length_reverse]
    omega
  have hd := TriangleAbsorption.disjoint_of_cover_length (C.append A.reverse) (E.append L.tail)
    hnew hET.isTrail _ hc hlen
  obtain ⟨U,hUi,hUj,hrest,hscore,hUa,hUb,_,_⟩ := replace_two_endpoints T L.index j hij
    s r t L.finish (C.append A.reverse) (E.append L.tail) hnew hET.isTrail hd hc
  have hUs : U.score=T.score := by
    rw [L.subgraph,hP,lollipop_vertex_card L.cycle L.isCycle L.tail L.isPath L.inter,
      lollipop_vertex_card C hnewC A.reverse hAB.of_append_left.reverse hCA,
      (walk_vertex_ncard_eq_iff _).mpr hp,(walk_vertex_ncard_eq_iff _).mpr hET,hform] at hscore
    simp only [C,Walk.length_append,Walk.length_reverse] at hscore
    omega
  let M : RootedCycleRep U s := ⟨L.index,r,hUa,hUb,C,A.reverse,hnewC,
    hAB.of_append_left.reverse,hCA,hUi⟩
  refine ⟨U,M,hUs,?_,?_,hUj,hrest⟩
  · simp only [M,C,Walk.length_append,Walk.length_reverse]
  · simp only [M,Walk.length_reverse]

lemma GloballyTailOptimized.ear_length_comparison {n : ℕ}
    {G : SimpleGraph (Fin n)} (D : GloballyTailOptimized G)
    (j : Fin (budget n)) (hij : D.rep.index ≠ j) {s t : Fin n}
    (A : G.Walk D.root s) (B : G.Walk s t) (E : G.Walk t D.root)
    (hrs : D.root ≠ s) (hst : s ≠ t) (htr : t ≠ D.root)
    (hform : D.rep.cycle=(A.append B).append E)
    (P : G.Walk s t) (hp : P.IsPath) (hP : (D.family.walk j).toSubgraph=P.toSubgraph)
    (hinter : ∀ x ∈ P.support, x ∈ D.rep.cycle.support → x=s ∨ x=t) :
    A.length+E.length ≤ P.length ∧
      (A.length+E.length=P.length → D.rep.tail.length ≤ min A.length E.length) := by
  obtain ⟨U,M,hUs,hMC,hMT,_,_⟩ := exchange_cycle_ear D.family D.root D.rep j hij
    A B E hrs hst htr hform P hp hP hinter
  have hlen : D.rep.cycle.length=A.length+B.length+E.length := by
    simp only [hform,Walk.length_append]
  have hmin := D.cycle_minimum U s M hUs
  rw [hMC,hlen] at hmin
  refine ⟨by omega,?_⟩
  intro heq
  have hTA : D.rep.tail.length ≤ A.length := by
    have hh := D.global_tail_minimum U s M hUs (by omega)
    rwa [hMT] at hh
  let L : RootedCycleRep D.family D.root :=
    ⟨D.rep.index,D.rep.finish,D.rep.start_eq,D.rep.finish_eq,D.rep.cycle.reverse,D.rep.tail,
      D.rep.isCycle.reverse,D.rep.isPath,
      by intro x hx ht; exact D.rep.inter x (by simpa using hx) ht,
      by simpa only [Walk.toSubgraph_append,Walk.toSubgraph_reverse] using D.rep.subgraph⟩
  have hrev : L.cycle=(E.reverse.append B.reverse).append A.reverse := by
    simp only [L,hform,Walk.reverse_append,Walk.append_assoc]
  obtain ⟨W,N,hWs,hNC,hNT,_,_⟩ := exchange_cycle_ear D.family D.root L j hij
    E.reverse B.reverse A.reverse htr.symm hst.symm hrs.symm hrev P.reverse hp.reverse
    (by simpa only [Walk.toSubgraph_reverse] using hP)
    (by
      intro x hxP hxC
      exact (hinter x (by simpa using hxP) (by simpa only [L,Walk.support_reverse,
        List.mem_reverse] using hxC)).symm)
  have hTE : D.rep.tail.length ≤ E.length := by
    simp only [Walk.length_reverse] at hNC hNT
    have hh := D.global_tail_minimum W t N hWs (by omega)
    rwa [hNT] at hh
  exact le_min hTA hTE

lemma two_edge_triangle_ear_forces_one_tail (F : MinimalFailure)
    (D : GloballyTailOptimized F.graph) (j : Fin (budget F.order)) (hij : D.rep.index ≠ j)
    {s t : Fin F.order} (hrs : F.graph.Adj D.root s) (hst : F.graph.Adj s t)
    (htr : F.graph.Adj t D.root)
    (hform : D.rep.cycle=Walk.cons hrs (Walk.cons hst (Walk.cons htr Walk.nil)))
    (P : F.graph.Walk s t) (hp : P.IsPath) (hP : (D.family.walk j).toSubgraph=P.toSubgraph)
    (hlen : P.length=2) (hav : D.root ∉ P.support) :
    D.rep.tail.length=1 := by
  let A := Walk.cons hrs Walk.nil
  let B := Walk.cons hst Walk.nil
  let E := Walk.cons htr Walk.nil
  have hh := GloballyTailOptimized.ear_length_comparison D j hij A B E
    hrs.ne hst.ne htr.ne (by simpa only [A,B,E,Walk.cons_append,Walk.nil_append] using hform)
    P hp hP (by
      intro x hxP hxC
      rw [hform] at hxC
      simp only [Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at hxC
      rcases hxC with hx|hx|hx|hx
      · exact (hav (hx ▸ hxP)).elim
      · exact Or.inl hx
      · exact Or.inr hx
      · exact (hav (hx ▸ hxP)).elim)
  have ht := hh.2 (by simp only [A,E,Walk.length_cons,Walk.length_nil,hlen])
  simp only [A,E,Walk.length_cons,Walk.length_nil,min_self] at ht
  have hpos := Walk.not_nil_iff_lt_length.mp (tail_not_nil F D.toOptimizedDefect)
  omega

end Erdos583GlobalCycleEarDevelopment
