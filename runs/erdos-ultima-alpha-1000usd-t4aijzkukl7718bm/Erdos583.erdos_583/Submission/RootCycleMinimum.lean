import Submission.SurplusNeighbor

/-! Root relocation at a globally shortest rooted cycle.
The minimization ranges over all roots at fixed incidence score and quota-square
energy. It does not assert that this minimum rules out every defect. -/

open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583Work.RootedTailSystem Erdos583Work.TrailNormalization
open Erdos583Work.LollipopEar Erdos583SurplusNeighborDevelopment
namespace Erdos583RootCycleMinimumDevelopment
open scoped Classical
set_option maxHeartbeats 1800000

lemma exists_global_shortest_cycle {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (hs : T.score+1=G.edgeSet.ncard+k) (hr : HasRoot T r) :
    ∃ U : TrailFamily G k, ∃ s : V, ∃ L : RootedCycleRep U s,
      U.score=T.score ∧ RootEnergy.quotaEnergy U=RootEnergy.quotaEnergy T ∧
      ∀ W : TrailFamily G k, ∀ t : V, ∀ M : RootedCycleRep W t,
        W.score=U.score → RootEnergy.quotaEnergy W=RootEnergy.quotaEnergy U →
          L.cycle.length ≤ M.cycle.length := by
  classical
  obtain ⟨R,hRs,hRq,_,⟨N⟩⟩ := exists_rooted_cycle_rep T r hs hr
  have hRE : RootEnergy.quotaEnergy R=RootEnergy.quotaEnergy T := by
    simp only [RootEnergy.quotaEnergy,hRq]
  let P (n : ℕ) := ∃ U : TrailFamily G k, ∃ s : V, ∃ L : RootedCycleRep U s,
    U.score=T.score ∧ RootEnergy.quotaEnergy U=RootEnergy.quotaEnergy T ∧ L.cycle.length=n
  have hex : ∃ n, P n := ⟨N.cycle.length,R,r,N,hRs,hRE,rfl⟩
  obtain ⟨U,s,L,hUs,hUE,hL⟩ := Nat.find_spec hex
  refine ⟨U,s,L,hUs,hUE,?_⟩
  intro W t M hWs hWE
  rw [hL]
  exact Nat.find_min' hex ⟨W,t,M,hWs.trans hUs,hWE.trans hUE,rfl⟩

/-- Build the explicit cycle-and-tail representative from a repeated start
whose suffix is simple, keeping the actual cycle length. -/
lemma rep_of_cons {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) {r x b : V}
    (ha : T.start i=r) (hb : T.finish i=b)
    (h : G.Adj r x) (p : G.Walk x b) (hp : p.IsPath)
    (ht : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph=(Walk.cons h p).toSubgraph) (hr : r ∈ p.support) :
    ∃ L : RootedCycleRep T r, L.index=i ∧
      L.cycle.length=1+(p.takeUntil r hr).length ∧
      L.tail.length=(p.dropUntil r hr).length := by
  let C := Walk.cons h (p.takeUntil r hr)
  let S := p.dropUntil r hr
  have hC : C.IsCycle := (Walk.cons_isCycle_iff _ h).mpr
    ⟨hp.takeUntil hr,fun hm ↦ (Walk.isTrail_cons h p).mp ht |>.2 (p.edges_takeUntil_subset hr hm)⟩
  have hS : S.IsPath := hp.dropUntil hr
  have hform : C.append S=Walk.cons h p := by
    simp only [C,S,Walk.cons_append,Walk.take_spec]
  have hinter (z : V) (hzC : z ∈ C.support) (hzS : z ∈ S.support) : z=r := by
    rcases (show z=r ∨ z ∈ (p.takeUntil r hr).support by
      simpa only [C,Walk.support_cons,List.mem_cons] using hzC) with hz | hz
    · exact hz
    · have hpath : ((p.takeUntil r hr).append (p.dropUntil r hr)).IsPath := by
        simpa only [Walk.take_spec] using hp
      by_contra hzr
      exact (hpath.ne_of_mem_support_of_append hzr hz hzS) rfl
  let L : RootedCycleRep T r := ⟨i,b,ha,hb,C,S,hC,hS,hinter,by rw [hform]; exact he⟩
  exact ⟨L,rfl,by simp only [L,C,Walk.length_cons,Nat.add_comm],rfl⟩

/-- If an outside path starts on the old cycle and its first edge reaches the
cycle's first neighbor, relocating the root strictly shortens the cycle.
The exterior path may intersect the lollipop arbitrarily otherwise. -/
lemma shorten_cycle_by_outside_terminal {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (L : RootedCycleRep T r)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (j : Fin k) (hij : L.index ≠ j)
    {x : V} (h : G.Adj r x) (R : G.Walk x r) (hC : L.cycle=Walk.cons h R)
    (f : G.Adj (T.start j) x) (q : G.Walk x (T.finish j))
    (hq : (Walk.cons f q).IsTrail)
    (hj : (T.walk j).toSubgraph=(Walk.cons f q).toSubgraph)
    (havoid : r ∉ (T.walk j).support) (hwC : T.start j ∈ L.cycle.support) :
    ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U (T.start j),
      U.score=T.score ∧ (∀ v, U.quota v=T.quota v) ∧ M.cycle.length < L.cycle.length := by
  rcases L with ⟨i,b,ha,hb,C,S,hcycle,hS,hinter,hsub⟩
  dsimp only at *
  subst r b C
  let p := R.append S
  have ht : (Walk.cons h p).IsTrail := by
    rw [←Walk.cons_append]
    exact trail_append_of_disjoint hcycle.isTrail hS.isTrail
      (edge_disjoint_of_one_common_vertex _ _ hinter)
  have hi : (T.walk i).toSubgraph=(Walk.cons h p).toSubgraph := by
    simpa only [Walk.cons_append] using hsub
  have hr : T.start i ∈ p.support := by
    exact (Walk.mem_support_append_iff R S).mpr (Or.inl R.end_mem_support)
  obtain ⟨hp,_,hother⟩ := simple_tail_of_one_defect_rep T hs i h p ht hi hr
  have hqp : (Walk.cons f q).IsPath :=
    ProtectedEdge.trail_isPath_of_subgraph_eq _ _ hq (hother j hij.symm) hj.symm
  obtain ⟨hw,U,hUs,hUq,_,hUi,_,hUa,hUb,_⟩ :=
    swap_to_outside_terminal T hm i j hij h p ht hi hr f q hqp hj havoid
  have hd : Disjoint (Walk.cons h p).toSubgraph.edgeSet (Walk.cons f q).toSubgraph.edgeSet := by
    rw [←hi,←hj]; exact T.disjoint hij
  have hfp := (exchange_first_edges_data h f p q ht hq hd).1
  obtain ⟨M,_,hMc,_⟩ := rep_of_cons U i hUa hUb f p hp hfp hUi hw
  have hwr : T.start j ≠ T.start i := fun he ↦ havoid (he ▸ (T.walk j).start_mem_support)
  have hwR : T.start j ∈ R.support := by
    rcases (show T.start j=T.start i ∨ T.start j ∈ R.support by
      simpa only [Walk.support_cons,List.mem_cons] using hwC) with hw | hw
    · exact (hwr hw).elim
    · exact hw
  have hlen := Walk.length_takeUntil_lt hwR hwr
  refine ⟨U,M,hUs,hUq,?_⟩
  rw [hMc]
  have htake : p.takeUntil (T.start j) hw=R.takeUntil (T.start j) hwR :=
    Walk.takeUntil_append_of_mem_left R S hwR
  rw [htake,Walk.length_cons]
  omega

/-- At a cycle minimum allowing changes of root, the outside terminal vertex
cannot lie on the cycle. -/
lemma global_minimum_terminal_not_on_cycle {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
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
    (havoid : r ∉ (T.walk j).support) : T.start j ∉ L.cycle.support := by
  intro hw
  obtain ⟨U,M,hUs,hUq,hLen⟩ := shorten_cycle_by_outside_terminal T r L hs hm
    j hij h R hC f q hq hj havoid hw
  have hUE : RootEnergy.quotaEnergy U=RootEnergy.quotaEnergy T := by
    simp only [RootEnergy.quotaEnergy,hUq]
  have hh := hmin U (T.start j) M hUs hUE
  omega

/-- The terminal vertex is forced into the tail, strictly outside the cycle.
This still requires an actual first-edge representative for the outside member. -/
lemma global_minimum_terminal_on_tail {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
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
    T.start j ∈ L.tail.support ∧ T.start j ∉ L.cycle.support := by
  have hn := global_minimum_terminal_not_on_cycle T r L hs hm hmin j hij h R hC f q hq hj havoid
  refine ⟨?_,hn⟩
  rcases L with ⟨i,b,ha,hb,C,S,hcycle,hS,hinter,hsub⟩
  dsimp only at *
  subst r b C
  let p := R.append S
  have ht : (Walk.cons h p).IsTrail := by
    rw [←Walk.cons_append]
    exact trail_append_of_disjoint hcycle.isTrail hS.isTrail
      (edge_disjoint_of_one_common_vertex _ _ hinter)
  have hi : (T.walk i).toSubgraph=(Walk.cons h p).toSubgraph := by
    simpa only [Walk.cons_append] using hsub
  have hr : T.start i ∈ p.support :=
    (Walk.mem_support_append_iff R S).mpr (Or.inl R.end_mem_support)
  have hother := (simple_tail_of_one_defect_rep T hs i h p ht hi hr).2.2
  have hqp : (Walk.cons f q).IsPath :=
    ProtectedEdge.trail_isPath_of_subgraph_eq _ _ hq (hother j hij.symm) hj.symm
  have hw := (swap_to_outside_terminal T hm i j hij h p ht hi hr f q hqp hj havoid).1
  rcases (Walk.mem_support_append_iff R S).mp hw with hw | hw
  · exact (hn (List.mem_cons_of_mem _ hw)).elim
  · exact hw

end Erdos583RootCycleMinimumDevelopment
