import Submission.MixedTriangleTailLock

/-! A one-edge triangular tail in a smallest failure has root degree at least seven. -/
namespace Erdos583TriangleOneTailDegreeSevenDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583ShortTriangleMixedCasesDevelopment Erdos583MixedTriangleTailLockDevelopment
open Erdos583ShortTriangleQuarticPairExclusionDevelopment Erdos583ShortTriangleIncidenceDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma failure_degree_five_short_triangle_only_mixed {n : ℕ}
    (hsmall : VertexCritical.SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (r : Fin n) (L : RootedCycleRep T r) {x y : Fin n}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hC : L.cycle=Walk.cons hrx (Walk.cons hxy (Walk.cons hry.symm Walk.nil)))
    (ht : L.tail.length=1 ∨ L.tail.length=2) (hd : Nat.card (G.neighborSet r)=5) :
    L.tail.length=2 ∧
      ((Nat.card (G.neighborSet x)=4 ∧ Nat.card (G.neighborSet y)=3) ∨
        (Nat.card (G.neighborSet x)=3 ∧ Nat.card (G.neighborSet y)=4)) := by
  rcases failure_degree_five_short_triangle_pair_cases hsmall hG hfail T hs hm r L hrx hxy hry hC ht hd with
    ⟨hx,hy⟩ | ⟨hx,hy⟩ | ⟨hx,hy⟩
  · have hh := failure_mixed_short_triangle_tail_lock hsmall hG hfail T hs hm r L hrx hxy hry hC ht hd hx hy
    exact ⟨hh.1,Or.inl ⟨hx,hy⟩⟩
  · let M : RootedCycleRep T r :=
      ⟨L.index,L.finish,L.start_eq,L.finish_eq,L.cycle.reverse,L.tail,L.isCycle.reverse,L.isPath,
        (fun z hz ht ↦ L.inter z (by simpa only [Walk.support_reverse,List.mem_reverse] using hz) ht),
        L.subgraph.trans (by simp only [Walk.toSubgraph_append,Walk.toSubgraph_reverse])⟩
    have hMC : M.cycle=Walk.cons hry (Walk.cons hxy.symm (Walk.cons hrx.symm Walk.nil)) := by
      change L.cycle.reverse=_
      rw [hC]
      rfl
    have hh := failure_mixed_short_triangle_tail_lock hsmall hG hfail T hs hm r M hry hxy.symm hrx hMC ht hd hy hx
    exact ⟨hh.1,Or.inr ⟨hx,hy⟩⟩
  · exact (failure_no_degree_five_short_triangle_quartic_pair hsmall hG hfail T hs hm r L
      hrx hxy hry hC ht hd hx hy).elim

lemma failure_one_tail_triangle_root_degree_ge_seven {n : ℕ}
    (hsmall : VertexCritical.SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (r : Fin n) (L : RootedCycleRep T r) (hc : L.cycle.length=3) (ht : L.tail.length=1) :
    7 ≤ Nat.card (G.neighborSet r) := by
  obtain ⟨_,ho,hlo⟩ := failure_any_short_triangle_root_degree hsmall hG hfail T hs hm r L hc (by omega)
  have hn5 : Nat.card (G.neighborSet r) ≠ 5 := by
    intro hd
    obtain ⟨x,y,hrx,hxy,hyr,hC⟩ := QuadrilateralAbsorption.three_cycle_rep L.cycle hc
    have hh := failure_degree_five_short_triangle_only_mixed hsmall hG hfail T hs hm r L
      hrx hxy hyr.symm hC (Or.inl ht) hd
    omega
  obtain ⟨m,hm⟩ := ho
  omega

end Erdos583TriangleOneTailDegreeSevenDevelopment
