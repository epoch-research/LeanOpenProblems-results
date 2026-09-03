import Submission.CubicTwinsReduction

/-! Cubic nonroot pairs are impossible at short triangular defects, regardless of root degree. -/
namespace Erdos583ShortTriangleCubicExclusionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583ShortTriangleIncidenceDevelopment Erdos583ShortTriangleDeletionDevelopment
open Erdos583CubicTriangleDeletionDevelopment Erdos583MixedTriangleTailLockDevelopment
open Erdos583ShortTriangleDistinctCubicExclusionDevelopment Erdos583CubicTwinsReductionDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma failure_no_short_triangle_cubic_pair {n : ℕ}
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
    (hdx : Nat.card (G.neighborSet x)=3) (hdy : Nat.card (G.neighborSet y)=3) : False := by
  obtain ⟨a,hxa,har,hay,hNx⟩ := cubic_third_neighbor hrx.symm hxy hry.ne hdx
  obtain ⟨b,hyb,hbr,hbx,hNy⟩ := cubic_third_neighbor hry.symm hxy.symm hrx.ne hdy
  by_cases hab : a=b
  · subst b
    have hc : L.cycle.length=3 := by rw [hC]; rfl
    have hrodd := (failure_any_short_triangle_root_degree hsmall hG hfail T hs hm r L hc (by omega)).2.1
    have hJ := short_triangle_delete_connected hG T hs hm r L hrx hxy hry hC ht hxa hyb har hay har hbx
    have hCe : L.cycle.toSubgraph.edgeSet=({s(r,x),s(x,y),s(r,y)} : Set (Sym2 (Fin n))) := by
      rw [hC]
      ext e
      simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,
        List.not_mem_nil,or_false,Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := y) (b := r)]
    have hx := short_triangle_external_link T hs hm r L hc ht
      (show x ∈ L.cycle.support by rw [hC]; simp) hrx.ne.symm hxa
      (by rw [hCe]; simp [hrx.ne.symm,hxy.ne,har,hay])
    rw [hCe] at hx
    obtain ⟨hK,hra,_⟩ := cubic_triangle_deletion_links hrx hry hxy hxa hyb har hay har hbx hNx hNy
      hJ (mem_support_of_reachable hrx.ne hx)
    exact hfail (cubic_twins_reduction hsmall hrx hry hxy hxa hyb har hNx hNy hrodd hK hra)
  · exact failure_no_short_triangle_distinct_cubic_data hsmall hG hfail T hs hm r L hrx hxy hry hC ht
      hdx hdy hxa hyb har hay hbr hbx hab hNx hNy

end Erdos583ShortTriangleCubicExclusionDevelopment
