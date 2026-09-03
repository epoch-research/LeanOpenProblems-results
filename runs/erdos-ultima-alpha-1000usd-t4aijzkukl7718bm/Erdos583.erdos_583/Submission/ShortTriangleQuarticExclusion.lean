import Submission.QuarticTriangleReduction

/-! Quartic nonroot pairs are impossible at short triangular defects, regardless of root degree. -/
namespace Erdos583ShortTriangleQuarticExclusionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583ShortTriangleDeletionDevelopment Erdos583QuarticPairProxyDevelopment
open Erdos583QuarticTriangleReductionDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma failure_no_short_triangle_quartic_pair {n : ℕ}
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
    (hdx : Nat.card (G.neighborSet x)=4) (hdy : Nat.card (G.neighborSet y)=4) : False := by
  obtain ⟨a,b,hxa,hxb,hab,hra,hrb,hya,hyb,hNx⟩ :=
    DegreeFourReduction.degree_four_other_neighbors hrx.symm hxy hry.ne hdx
  obtain ⟨c,d,hyc,hyd,hcd,hrc,hrd,hxc,hxd,hNy⟩ :=
    DegreeFourReduction.degree_four_other_neighbors hry.symm hxy.symm hrx.ne hdy
  let F : QuarticData G r x y a b c d :=
    ⟨hrx,hxy,hry,hxa,hxb,hyc,hyd,hra.symm,hrb.symm,hya.symm,hyb.symm,
      hrc.symm,hrd.symm,hxc.symm,hxd.symm,hab,hcd,hNx,hNy⟩
  have hJ := short_triangle_delete_connected hG T hs hm r L hrx hxy hry hC ht hxa hyc
    hra.symm hya.symm hrc.symm hxc.symm
  have hc : L.cycle.length=3 := by rw [hC]; rfl
  have hCe : L.cycle.toSubgraph.edgeSet=({s(r,x),s(x,y),s(r,y)} : Set (Sym2 (Fin n))) := by
    rw [hC]
    ext e
    simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,
      List.not_mem_nil,or_false,Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := y) (b := r)]
  have hx := short_triangle_external_link T hs hm r L hc ht
    (show x ∈ L.cycle.support by rw [hC]; simp) hrx.ne.symm hxa
    (by rw [hCe]; simp [hrx.ne.symm,hxy.ne,hra.symm,hya.symm])
  rw [hCe] at hx
  exact failure_no_quartic_triangle_data hsmall hG hfail F hJ (mem_support_of_reachable hrx.ne hx)

end Erdos583ShortTriangleQuarticExclusionDevelopment
