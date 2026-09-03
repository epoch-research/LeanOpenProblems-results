import Submission.ShortTriangleDeletion

/-! Cubic/quartic nonroot pairs are impossible at any short triangular defect. -/
namespace Erdos583ShortTriangleMixedExclusionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583ShortTriangleIncidenceDevelopment Erdos583ShortTriangleDeletionDevelopment
open Erdos583MixedOddTriangleReductionDevelopment Erdos583MixedTriangleTailLockDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma failure_no_short_triangle_mixed_pair {n : ℕ}
    (hsmall : VertexCritical.SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (r : Fin n) (L : RootedCycleRep T r) {x y : Fin n}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hC : L.cycle=Walk.cons hrx (Walk.cons hxy (Walk.cons hry.symm Walk.nil)))
    (ht : L.tail.length=1 ∨ L.tail.length=2)
    (hdx : Nat.card (G.neighborSet x)=4) (hdy : Nat.card (G.neighborSet y)=3) : False := by
  obtain ⟨a,b,hxa,hxb,hab,hra,hrb,hya,hyb,hNx⟩ :=
    DegreeFourReduction.degree_four_other_neighbors hrx.symm hxy hry.ne hdx
  obtain ⟨c,hyc,hcr,hcx,hNy⟩ := cubic_third_neighbor hry.symm hxy.symm hrx.ne hdy
  have hc : L.cycle.length=3 := by rw [hC]; rfl
  have hrodd := (failure_any_short_triangle_root_degree hsmall hG hfail T hs hm r L hc (by omega)).2.1
  have hF := short_triangle_delete_connected hG T hs hm r L hrx hxy hry hC ht hxa hyc
    hra.symm hya.symm hcr hcx
  exact hfail (mixed_odd_triangle_reduction hsmall hG hrx hxy hry hxa hxb hyc
    hra.symm hrb.symm hya.symm hyb.symm hab hcr hcx hNx hNy hrodd hF)

end Erdos583ShortTriangleMixedExclusionDevelopment
