import Submission.CubicTriangleExclusion

/-! A remaining degree-four vertex in the degree-five short-triangle branch. -/
namespace Erdos583ShortTriangleDegreeFourDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583ShortTriangleIncidenceDevelopment Erdos583CubicTriangleExclusionDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma failure_degree_five_short_triangle_has_degree_four {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (r : Fin n) (L : RootedCycleRep T r) {x y : Fin n}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hC : L.cycle=Walk.cons hrx (Walk.cons hxy (Walk.cons hry.symm Walk.nil)))
    (ht : L.tail.length=1 ∨ L.tail.length=2) (hd : Nat.card (G.neighborSet r)=5) :
    (Nat.card (G.neighborSet x)=4 ∧ T.quota x=0) ∨
      (Nat.card (G.neighborSet y)=4 ∧ T.quota y=0) := by
  have hc : L.cycle.length=3 := by rw [hC]; rfl
  have hxC : x ∈ L.cycle.support := by rw [hC]; simp
  have hyC : y ∈ L.cycle.support := by rw [hC]; simp
  have hxhi := failure_short_triangle_other_cycle_degree hsmall hG hfail T hs hm r L hc ht hxC hrx.ne.symm
  have hyhi := failure_short_triangle_other_cycle_degree hsmall hG hfail T hs hm r L hc ht hyC hry.ne.symm
  rw [hd] at hxhi hyhi
  have hxlo : 2 ≤ Nat.card (G.neighborSet x) := by
    have hh := Set.ncard_mono (show ({r,y} : Set (Fin n)) ⊆ G.neighborSet x by
      rintro v (rfl|rfl); exact hrx.symm; exact hxy)
    simpa only [Set.ncard_pair hry.ne,←Nat.card_coe_set_eq] using hh
  have hylo : 2 ≤ Nat.card (G.neighborSet y) := by
    have hh := Set.ncard_mono (show ({r,x} : Set (Fin n)) ⊆ G.neighborSet y by
      rintro v (rfl|rfl); exact hry.symm; exact hxy.symm)
    simpa only [Set.ncard_pair hrx.ne,←Nat.card_coe_set_eq] using hh
  by_cases hx : Nat.card (G.neighborSet x)=4
  · exact Or.inl ⟨hx,by omega⟩
  by_cases hy : Nat.card (G.neighborSet y)=4
  · exact Or.inr ⟨hy,by omega⟩
  have hxn2 : Nat.card (G.neighborSet x) ≠ 2 := by
    intro hx2
    have hh := LowDegreeAdjacency.degree_two_neighbors_ge_four hsmall hG hfail hxy hx2
    omega
  have hyn2 : Nat.card (G.neighborSet y) ≠ 2 := by
    intro hy2
    have hh := LowDegreeAdjacency.degree_two_neighbors_ge_four hsmall hG hfail hxy.symm hy2
    omega
  exact (failure_no_degree_five_short_triangle_cubic_pair hsmall hG hfail T hs hm r L
    hrx hxy hry hC ht hd (by omega) (by omega)).elim

end Erdos583ShortTriangleDegreeFourDevelopment
