import Submission.ShortTriangleCubicExclusion

/-! At least one nonroot vertex of a short triangular defect has degree at least five. -/
namespace Erdos583ShortTriangleNonrootBoundDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583ShortTriangleCubicExclusionDevelopment Erdos583ShortTriangleMixedExclusionDevelopment
open Erdos583ShortTriangleQuarticExclusionDevelopment Erdos583DegreeTwoNeighborFiveDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

def reverse_cycle_rep {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (L : RootedCycleRep T r) : RootedCycleRep T r :=
  { L with
    cycle := L.cycle.reverse
    isCycle := L.isCycle.reverse
    inter := by simpa only [Walk.support_reverse,List.mem_reverse] using L.inter
    subgraph := by
      rw [Walk.toSubgraph_append,Walk.toSubgraph_reverse,←Walk.toSubgraph_append]
      exact L.subgraph }

lemma failure_short_triangle_nonroot_degree_ge_five {n : ℕ}
    (hsmall : VertexCritical.SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (r : Fin n) (L : RootedCycleRep T r) {x y : Fin n}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hC : L.cycle=Walk.cons hrx (Walk.cons hxy (Walk.cons hry.symm Walk.nil)))
    (ht : L.tail.length=1 ∨ L.tail.length=2) :
    5 ≤ Nat.card (G.neighborSet x) ∨ 5 ≤ Nat.card (G.neighborSet y) := by
  by_contra hnot
  have hdx : Nat.card (G.neighborSet x) ≤ 4 := by omega
  have hdy : Nat.card (G.neighborSet y) ≤ 4 := by omega
  have hxlo : 2 ≤ Nat.card (G.neighborSet x) := by
    have hh := Set.ncard_le_ncard (show ({r,y} : Set (Fin n)) ⊆ G.neighborSet x from by
      rintro z (rfl|rfl); exact hrx.symm; exact hxy)
    simpa only [Set.ncard_pair hry.ne,←Nat.card_coe_set_eq] using hh
  have hylo : 2 ≤ Nat.card (G.neighborSet y) := by
    have hh := Set.ncard_le_ncard (show ({r,x} : Set (Fin n)) ⊆ G.neighborSet y from by
      rintro z (rfl|rfl); exact hry.symm; exact hxy.symm)
    simpa only [Set.ncard_pair hrx.ne,←Nat.card_coe_set_eq] using hh
  have hxne : Nat.card (G.neighborSet x) ≠ 2 := by
    intro hh
    have hh' := degree_two_neighbors_ge_five hsmall hG hfail hxy hh
    omega
  have hyne : Nat.card (G.neighborSet y) ≠ 2 := by
    intro hh
    have hh' := degree_two_neighbors_ge_five hsmall hG hfail hxy.symm hh
    omega
  rcases (show Nat.card (G.neighborSet x)=3 ∨ Nat.card (G.neighborSet x)=4 by omega) with hx | hx
  · rcases (show Nat.card (G.neighborSet y)=3 ∨ Nat.card (G.neighborSet y)=4 by omega) with hy | hy
    · exact failure_no_short_triangle_cubic_pair hsmall hG hfail T hs hm r L hrx hxy hry hC ht hx hy
    · let M := reverse_cycle_rep T r L
      have hMC : M.cycle=Walk.cons hry (Walk.cons hxy.symm (Walk.cons hrx.symm Walk.nil)) := by
        change L.cycle.reverse=_
        rw [hC]
        rfl
      exact failure_no_short_triangle_mixed_pair hsmall hG hfail T hs hm r M hry hxy.symm hrx hMC ht hy hx
  · rcases (show Nat.card (G.neighborSet y)=3 ∨ Nat.card (G.neighborSet y)=4 by omega) with hy | hy
    · exact failure_no_short_triangle_mixed_pair hsmall hG hfail T hs hm r L hrx hxy hry hC ht hx hy
    · exact failure_no_short_triangle_quartic_pair hsmall hG hfail T hs hm r L hrx hxy hry hC ht hx hy

end Erdos583ShortTriangleNonrootBoundDevelopment
