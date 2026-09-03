import Submission.LollipopEndpointRotation

/-! A short tail in an unrestricted cycle minimum has no shared root endpoint. -/
namespace Erdos583RootEndpointTailCapacityDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583LollipopEndpointRotationDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma path_same_predecessor_same_successor {V : Type*} {G : SimpleGraph V} {r b w x y : V}
    (P : G.Walk r b) (hp : P.IsPath)
    (A : G.Walk r w) (f : G.Adj w x) (B : G.Walk x b)
    (D : G.Walk r w) (g : G.Adj w y) (E : G.Walk y b)
    (hP : P=A.append (Walk.cons f B)) (hP' : P=D.append (Walk.cons g E)) : x=y := by
  have ha : A.length ≤ P.length := by rw [hP,Walk.length_append]; omega
  have hd : D.length ≤ P.length := by rw [hP',Walk.length_append]; omega
  have haw : P.getVert A.length=w := by rw [hP,Walk.getVert_append]; simp
  have hdw : P.getVert D.length=w := by rw [hP',Walk.getVert_append]; simp
  have he := hp.getVert_injOn ha hd (haw.trans hdw.symm)
  have hax : P.getVert (A.length+1)=x := by rw [hP,Walk.getVert_append]; simp
  have hdy : P.getVert (D.length+1)=y := by rw [hP',Walk.getVert_append]; simp
  rw [he] at hax
  exact hax.symm.trans hdy

lemma short_walk_nonstart_unique {V : Type*} {G : SimpleGraph V} {r b x y : V}
    (P : G.Walk r b) (hl : P.length ≤ 1)
    (hx : x ∈ P.support) (hy : y ∈ P.support) (hxr : x ≠ r) (hyr : y ≠ r) : x=y := by
  cases P with
  | nil => simp only [Walk.support_nil,List.mem_singleton] at hx; exact (hxr hx).elim
  | cons h P =>
    have hn : P.Nil := Walk.nil_iff_length_eq.mpr (by simp only [Walk.length_cons] at hl; omega)
    cases hn
    simp only [Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at hx hy
    exact (hx.resolve_left hxr).trans (hy.resolve_left hyr).symm

lemma minimum_shared_root_tail_length_ge_two {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r)
    (hmin : ∀ W : TrailFamily G k, ∀ s : V, ∀ M : RootedCycleRep W s,
      W.score=T.score → L.cycle.length ≤ M.cycle.length)
    (j : Fin k) (hij : L.index ≠ j) {b : V}
    (P : G.Walk r b) (hp : P.IsPath) (hj : (T.walk j).toSubgraph=P.toSubgraph) :
    2 ≤ L.tail.length := by
  obtain ⟨w,A,f,B,hP,hwS,hwC⟩ := minimum_lollipop_root_path_predecessor T hm r L hmin j hij
    (L.cycle.toSubgraph_adj_snd L.isCycle.not_nil) P hp hj
  obtain ⟨z,D,g,E,hP',hzS,hzC⟩ := minimum_lollipop_root_path_predecessor T hm r L hmin j hij
    ((L.cycle.toSubgraph_adj_penultimate L.isCycle.not_nil).symm) P hp hj
  have hwr : w ≠ r := fun he ↦ hwC (he ▸ L.cycle.start_mem_support)
  have hzr : z ≠ r := fun he ↦ hzC (he ▸ L.cycle.start_mem_support)
  by_contra hlen
  have hwz := short_walk_nonstart_unique L.tail (by omega) hwS hzS hwr hzr
  subst z
  exact L.isCycle.snd_ne_penultimate (path_same_predecessor_same_successor P hp A f B D g E hP hP')

lemma minimum_short_tail_other_endpoints_avoid_root {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r)
    (hmin : ∀ W : TrailFamily G k, ∀ s : V, ∀ M : RootedCycleRep W s,
      W.score=T.score → L.cycle.length ≤ M.cycle.length)
    (hl : L.tail.length ≤ 1) :
    ∀ j, j ≠ L.index → T.start j ≠ r ∧ T.finish j ≠ r := by
  intro j hji
  have hp := (T.one_defect_other_paths hs L.index L.member_not_path).2 j hji
  have hends {a b : V} (P : G.Walk a b) (hP : P.IsPath)
      (hj : (T.walk j).toSubgraph=P.toSubgraph) : a ≠ r := by
    rintro rfl
    have hh := minimum_shared_root_tail_length_ge_two T hm a L hmin j hji.symm P hP hj
    omega
  exact ⟨hends (T.walk j) hp rfl,
    hends (T.walk j).reverse hp.reverse (Walk.toSubgraph_reverse _).symm⟩

lemma minimum_one_edge_tail_root_quota_one {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r)
    (hmin : ∀ W : TrailFamily G k, ∀ s : V, ∀ M : RootedCycleRep W s,
      W.score=T.score → L.cycle.length ≤ M.cycle.length)
    (hl : L.tail.length=1) : T.quota r=1 := by
  have hbr : L.finish ≠ r := by
    intro he
    have hnil {a b : V} (P : G.Walk a b) (hp : P.IsPath) (hab : b=a) : P.Nil := by
      subst b
      exact Walk.nil_iff_eq_nil.mpr ((Walk.isPath_iff_eq_nil P).mp hp)
    have hz := Walk.nil_iff_length_eq.mp (hnil L.tail L.isPath he)
    omega
  classical
  have hother := minimum_short_tail_other_endpoints_avoid_root T hs hm r L hmin (by omega)
  rw [quota_eq_sum_endpoints,Finset.sum_eq_single L.index]
  · simp [L.start_eq,L.finish_eq,hbr]
  · intro j _ hji
    simp only [if_neg (hother j hji).1,if_neg (hother j hji).2,add_zero]
  · simp

lemma minimum_even_root_not_one_edge_tail {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r)
    (hmin : ∀ W : TrailFamily G k, ∀ s : V, ∀ M : RootedCycleRep W s,
      W.score=T.score → L.cycle.length ≤ M.cycle.length)
    (he : Even (Nat.card (G.neighborSet r))) : L.tail.length ≠ 1 := by
  intro hl
  have hq := minimum_one_edge_tail_root_quota_one T hs hm r L hmin hl
  have hh := (QuotaParity.quota_even_iff T r).mpr he
  rw [hq] at hh
  norm_num at hh

end Erdos583RootEndpointTailCapacityDevelopment
