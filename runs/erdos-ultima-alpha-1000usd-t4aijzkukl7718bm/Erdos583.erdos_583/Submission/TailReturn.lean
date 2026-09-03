import Submission.Work

/-! A second routing for an outside terminal on the lollipop tail.
Avoiding the tail prefix repairs the defect. No internal-rootification
principle is assumed here. -/

open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583Work.RootedTailSystem Erdos583Work.TrailNormalization
open Erdos583Work.LollipopEar
namespace Erdos583TailReturnDevelopment
open scoped Classical
set_option maxHeartbeats 1800000

lemma tail_return_routing {V : Type*} {G : SimpleGraph V} {r x w b c : V}
    (h : G.Adj r x) (R : G.Walk x r) (S : G.Walk r w) (B : G.Walk w b)
    (hc : (Walk.cons h R).IsCycle) (ht : (S.append B).IsPath)
    (hi : ∀ z ∈ (Walk.cons h R).support, z ∈ (S.append B).support → z=r)
    (hwr : w ≠ r) (f : G.Adj w x) (q : G.Walk x c)
    (hp : (Walk.cons f q).IsPath)
    (hd : Disjoint ((Walk.cons h R).append (S.append B)).toSubgraph.edgeSet
      (Walk.cons f q).toSubgraph.edgeSet)
    (havoid : ∀ z ∈ S.support, z ∉ q.support) :
    (R.reverse.append (Walk.cons f.symm B)).IsPath ∧
      (S.reverse.append (Walk.cons h q)).IsPath ∧
      Disjoint (R.reverse.append (Walk.cons f.symm B)).toSubgraph.edgeSet
        (S.reverse.append (Walk.cons h q)).toSubgraph.edgeSet ∧
      (R.reverse.append (Walk.cons f.symm B)).toSubgraph.edgeSet ∪
        (S.reverse.append (Walk.cons h q)).toSubgraph.edgeSet =
      ((Walk.cons h R).append (S.append B)).toSubgraph.edgeSet ∪
        (Walk.cons f q).toSubgraph.edgeSet := by
  have hR : R.IsPath := (Walk.cons_isCycle_iff R h).mp hc |>.1
  have hSC (z) (hz : z ∈ S.support) : z ∈ (S.append B).support :=
    (Walk.mem_support_append_iff S B).mpr (Or.inl hz)
  have hBC (z) (hz : z ∈ B.support) : z ∈ (S.append B).support :=
    (Walk.mem_support_append_iff S B).mpr (Or.inr hz)
  have hrB : r ∉ B.support := by
    intro hr
    exact (ht.ne_of_mem_support_of_append hwr.symm S.start_mem_support hr) rfl
  have hRB (z) (hz : z ∈ R.support) : z ∉ B.support := by
    intro hb
    exact hrB ((hi z (List.mem_cons_of_mem _ hz) (hBC z hb)) ▸ hb)
  have hxB : x ∉ B.support := hRB x R.start_mem_support
  have hA : (R.reverse.append (Walk.cons f.symm B)).IsPath := by
    apply path_append_of_support_intersection hR.reverse
      ((Walk.cons_isPath_iff f.symm B).mpr ⟨ht.of_append_right,hxB⟩)
    intro z hz hz'
    rcases (show z=x ∨ z ∈ B.support by simpa only [Walk.support_cons,List.mem_cons] using hz') with hz' | hz'
    · exact hz'
    · exact (hRB z (by simpa only [Walk.support_reverse,List.mem_reverse] using hz) hz').elim
  have hrq : r ∉ q.support := havoid r S.start_mem_support
  have hZ : (S.reverse.append (Walk.cons h q)).IsPath := by
    apply path_append_of_support_intersection ht.of_append_left.reverse
      ((Walk.cons_isPath_iff h q).mpr ⟨hp.of_cons,hrq⟩)
    intro z hz hz'
    rcases (show z=r ∨ z ∈ q.support by simpa only [Walk.support_cons,List.mem_cons] using hz') with hz' | hz'
    · exact hz'
    · exact (havoid z (by simpa only [Walk.support_reverse,List.mem_reverse] using hz) hz').elim
  have hct := edge_disjoint_of_one_common_vertex (Walk.cons h R) (S.append B) hi
  have hsb := append_trail_disjoint ht.isTrail
  have hhr : s(r,x) ∉ R.toSubgraph.edgeSet := by
    rw [Walk.mem_edges_toSubgraph]
    exact (Walk.isTrail_cons h R).mp hc.isTrail |>.2
  have hfq : s(w,x) ∉ q.toSubgraph.edgeSet := by
    rw [Walk.mem_edges_toSubgraph]
    exact (Walk.isTrail_cons f q).mp hp.isTrail |>.2
  refine ⟨hA,hZ,?_,?_⟩
  · apply Set.disjoint_left.mpr
    intro e he he'
    have h1 := (Set.disjoint_left.mp hd) (a := e)
    have h2 := (Set.disjoint_left.mp hct) (a := e)
    have h3 := (Set.disjoint_left.mp hsb) (a := e)
    simp only [Walk.toSubgraph_append,Walk.toSubgraph_reverse,Walk.toSubgraph,
      Subgraph.edgeSet_sup,edgeSet_subgraphOfAdj,Set.singleton_union,Set.mem_union,
      Set.mem_insert_iff,Sym2.eq_swap (a := x) (b := w)] at h1 h2 he he'
    rcases he with he | he | he <;> rcases he' with he' | he' | he'
    · exact h2 (Or.inr he) (Or.inl he')
    · exact hhr (he' ▸ he)
    · exact h1 (Or.inl (Or.inr he)) (Or.inr he')
    · exact h1 (Or.inr (Or.inl he')) (Or.inl he)
    · exact h1 (Or.inl (Or.inl he')) (Or.inl he)
    · exact hfq (he ▸ he')
    · exact h3 he' he
    · exact h2 (Or.inl he') (Or.inr he)
    · exact h1 (Or.inr (Or.inr he)) (Or.inr he')
  · ext e
    simp only [Walk.toSubgraph_append,Walk.toSubgraph_reverse,Walk.toSubgraph,
      Subgraph.edgeSet_sup,edgeSet_subgraphOfAdj,Set.singleton_union,Set.mem_union,
      Set.mem_insert_iff,Sym2.eq_swap (a := x) (b := w)]
    tauto

lemma maximum_tail_return {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i j : Fin k) (hij : i ≠ j) {r x w b c : V}
    (h : G.Adj r x) (R : G.Walk x r) (S : G.Walk r w) (B : G.Walk w b)
    (hc : (Walk.cons h R).IsCycle) (ht : (S.append B).IsPath)
    (hi : ∀ z ∈ (Walk.cons h R).support, z ∈ (S.append B).support → z=r)
    (hwr : w ≠ r) (f : G.Adj w x) (q : G.Walk x c)
    (hp : (Walk.cons f q).IsPath)
    (hL : (T.walk i).toSubgraph=((Walk.cons h R).append (S.append B)).toSubgraph)
    (hP : (T.walk j).toSubgraph=(Walk.cons f q).toSubgraph) :
    ∃ z, z ∈ S.support ∧ z ∈ q.support := by
  classical
  by_contra! hn
  obtain ⟨hA,hZ,hd,hu⟩ := tail_return_routing h R S B hc ht hi hwr f q hp
    (by rw [←hL,←hP]; exact T.disjoint hij) hn
  obtain ⟨U,_,_,_,hUs⟩ := GeneralPair.replace_two T i j hij r b w c
    (R.reverse.append (Walk.cons f.symm B)) (S.reverse.append (Walk.cons h q))
    hA.isTrail hZ.isTrail hd (by rw [hu,←hL,←hP])
  rw [hL,hP,lollipop_vertex_card (Walk.cons h R) hc (S.append B) ht hi,
    (walk_vertex_ncard_eq_iff _).mpr hp,(walk_vertex_ncard_eq_iff _).mpr hA,
    (walk_vertex_ncard_eq_iff _).mpr hZ] at hUs
  simp only [Walk.length_append,Walk.length_cons,Walk.length_reverse] at hUs
  have hh := hm U
  omega

/-- At a global cycle minimum, the outside path must return to the strict
interior of the tail prefix before its starting point. -/
lemma global_minimum_tail_return {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (L : RootedCycleRep T r)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hmin : ∀ W : TrailFamily G k, ∀ t : V, ∀ M : RootedCycleRep W t,
      W.score=T.score → RootEnergy.quotaEnergy W=RootEnergy.quotaEnergy T →
        L.cycle.length ≤ M.cycle.length)
    (j : Fin k) (hij : L.index ≠ j)
    {x : V} (h : G.Adj r x) (R : G.Walk x r) (hC : L.cycle=Walk.cons h R)
    (f : G.Adj (T.start j) x) (q : G.Walk x (T.finish j))
    (hq : (Walk.cons f q).IsTrail)
    (hj : (T.walk j).toSubgraph=(Walk.cons f q).toSubgraph)
    (havoid : r ∉ (T.walk j).support) :
    ∃ hw : T.start j ∈ L.tail.support, ∃ z,
      z ∈ (L.tail.takeUntil (T.start j) hw).support ∧ z ∈ q.support ∧
      z ≠ r ∧ z ≠ T.start j := by
  obtain ⟨hw,_⟩ := RootCycleMinimum.global_minimum_terminal_on_tail T r L hs hm hmin
    j hij h R hC f q hq hj havoid
  have hqp : (Walk.cons f q).IsPath :=
    ProtectedEdge.trail_isPath_of_subgraph_eq _ _ hq
      ((T.one_defect_other_paths hs L.index L.member_not_path).2 j hij.symm) hj.symm
  have hwr : T.start j ≠ r := fun he ↦ havoid (he ▸ (T.walk j).start_mem_support)
  have hrq : r ∉ q.support := by
    intro hv
    apply havoid
    rw [←Walk.mem_verts_toSubgraph,hj,Walk.mem_verts_toSubgraph]
    exact List.mem_cons_of_mem _ hv
  have hwq : T.start j ∉ q.support := (Walk.cons_isPath_iff f q).mp hqp |>.2
  have he : (T.walk L.index).toSubgraph=
      ((Walk.cons h R).append ((L.tail.takeUntil (T.start j) hw).append
        (L.tail.dropUntil (T.start j) hw))).toSubgraph := by
    rw [Walk.take_spec,←hC]
    exact L.subgraph
  obtain ⟨z,hz,hzq⟩ := maximum_tail_return T hm L.index j hij h R
    (L.tail.takeUntil (T.start j) hw) (L.tail.dropUntil (T.start j) hw)
    (hC ▸ L.isCycle) (by simpa only [Walk.take_spec] using L.isPath)
    (by simpa only [Walk.take_spec,←hC] using L.inter) hwr f q hqp he hj
  exact ⟨hw,z,hz,hzq,fun he ↦ hrq (he ▸ hzq),fun he ↦ hwq (he ▸ hzq)⟩

lemma length_ge_two_of_internal_vertex {V : Type*} {G : SimpleGraph V} {a b z : V}
    (p : G.Walk a b) (hz : z ∈ p.support) (hza : z ≠ a) (hzb : z ≠ b) :
    2 ≤ p.length := by
  cases p with
  | nil => simp_all
  | cons h p =>
    cases p with
    | nil => simp_all
    | cons h' p => simp

lemma global_minimum_terminal_distance {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (L : RootedCycleRep T r)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hmin : ∀ W : TrailFamily G k, ∀ t : V, ∀ M : RootedCycleRep W t,
      W.score=T.score → RootEnergy.quotaEnergy W=RootEnergy.quotaEnergy T →
        L.cycle.length ≤ M.cycle.length)
    (j : Fin k) (hij : L.index ≠ j)
    {x : V} (h : G.Adj r x) (R : G.Walk x r) (hC : L.cycle=Walk.cons h R)
    (f : G.Adj (T.start j) x) (q : G.Walk x (T.finish j))
    (hq : (Walk.cons f q).IsTrail)
    (hj : (T.walk j).toSubgraph=(Walk.cons f q).toSubgraph)
    (havoid : r ∉ (T.walk j).support) :
    ∃ hw : T.start j ∈ L.tail.support,
      2 ≤ (L.tail.takeUntil (T.start j) hw).length := by
  obtain ⟨hw,z,hz,_,hzr,hzw⟩ := global_minimum_tail_return T r L hs hm hmin j hij h R hC f q hq hj havoid
  exact ⟨hw,length_ge_two_of_internal_vertex _ hz hzr hzw⟩

end Erdos583TailReturnDevelopment
