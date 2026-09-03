import Submission.LockedMixedTriangleReduction

/-! Every short triangular defect in a smallest failure has root degree at least seven. -/
namespace Erdos583ShortTriangleDegreeSevenDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583ShortTriangleIncidenceDevelopment Erdos583ShortTriangleQuarticPairExclusionDevelopment
open Erdos583MixedTriangleTailLockDevelopment Erdos583MixedTriangleTerminalExclusionDevelopment
open Erdos583LockedMixedTriangleReductionDevelopment Erdos583TriangleOneTailDegreeSevenDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma failure_no_mixed_degree_five_short_triangle {n : ℕ}
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
    (hdx : Nat.card (G.neighborSet x)=4) (hdy : Nat.card (G.neighborSet y)=3) : False := by
  obtain ⟨hlen,a,b,c,hxa,hxb,hyc,_,har,hbr,_,_,hcr,hcx,_,habT,_,hNy⟩ :=
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
  have hNx := four_neighbors_exhaust hrx.symm hxy hxs hxt hry.ne hrs.ne.symm F.tr F.sy F.ty hst.ne hdx
  exact hfail (locked_mixed_triangle_reduction hsmall hG F hxs hxt hyc hcr hcx hNx hNy)

lemma failure_no_degree_five_short_triangle {n : ℕ}
    (hsmall : VertexCritical.SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (r : Fin n) (L : RootedCycleRep T r) (hc : L.cycle.length=3)
    (ht : L.tail.length=1 ∨ L.tail.length=2) (hd : Nat.card (G.neighborSet r)=5) : False := by
  obtain ⟨x,y,hrx,hxy,hyr,hC⟩ := QuadrilateralAbsorption.three_cycle_rep L.cycle hc
  obtain ⟨_,hmix⟩ := failure_degree_five_short_triangle_only_mixed hsmall hG hfail T hs hm r L
    hrx hxy hyr.symm hC ht hd
  rcases hmix with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · exact failure_no_mixed_degree_five_short_triangle hsmall hG hfail T hs hm r L hrx hxy hyr.symm hC ht hd hx hy
  · let M : RootedCycleRep T r :=
      ⟨L.index,L.finish,L.start_eq,L.finish_eq,L.cycle.reverse,L.tail,L.isCycle.reverse,L.isPath,
        (fun z hz ht ↦ L.inter z (by simpa only [Walk.support_reverse,List.mem_reverse] using hz) ht),
        L.subgraph.trans (by simp only [Walk.toSubgraph_append,Walk.toSubgraph_reverse])⟩
    have hMC : M.cycle=Walk.cons hyr.symm (Walk.cons hxy.symm (Walk.cons hrx.symm Walk.nil)) := by
      change L.cycle.reverse=_
      rw [hC]
      rfl
    exact failure_no_mixed_degree_five_short_triangle hsmall hG hfail T hs hm r M hyr.symm hxy.symm hrx hMC ht hd hy hx

lemma failure_short_triangle_root_degree_ge_seven {n : ℕ}
    (hsmall : VertexCritical.SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (r : Fin n) (L : RootedCycleRep T r) (hc : L.cycle.length=3)
    (ht : L.tail.length=1 ∨ L.tail.length=2) : 7 ≤ Nat.card (G.neighborSet r) := by
  obtain ⟨_,ho,hlo⟩ := failure_any_short_triangle_root_degree hsmall hG hfail T hs hm r L hc (by omega)
  have hn5 : Nat.card (G.neighborSet r) ≠ 5 :=
    failure_no_degree_five_short_triangle hsmall hG hfail T hs hm r L hc ht
  obtain ⟨m,hm⟩ := ho
  omega

end Erdos583ShortTriangleDegreeSevenDevelopment
