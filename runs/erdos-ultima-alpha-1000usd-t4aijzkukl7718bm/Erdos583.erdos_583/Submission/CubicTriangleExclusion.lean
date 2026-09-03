import Submission.CubicTriangleEvenAttachment

/-! Excluding a cubic pair with an odd triangle root and a common path carrier. -/
namespace Erdos583CubicTriangleExclusionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583CubicTriangleCarrierDevelopment Erdos583CubicTriangleEvenChordDevelopment
open Erdos583CubicTrianglePunctureDevelopment Erdos583CubicTriangleEvenAttachmentDevelopment
open Erdos583ShortTriangleSingleCarrierDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma failure_no_odd_root_cubic_triangle_carrier {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {r x y : Fin n} (hrx : G.Adj r x) (hry : G.Adj r y) (hxy : G.Adj x y)
    (hrodd : Odd (Nat.card (G.neighborSet r)))
    (hdx : Nat.card (G.neighborSet x)=3) (hdy : Nat.card (G.neighborSet y)=3)
    (P : G.Walk x y) (hP : P.IsPath) (hrP : r ∈ P.support)
    (hnrx : s(r,x) ∉ P.edges) (hnry : s(r,y) ∉ P.edges) (hnxy : s(x,y) ∉ P.edges) : False := by
  obtain ⟨a,b,hxa,hyb,har,hay,hbr,hbx,hab,_,hnab,_,haeven,_⟩ :=
    failure_cubic_triangle_carrier_even_chord hsmall hG hfail hrx hry hxy hrodd hdx hdy P hP hrP hnrx hnry hnxy
  have hNx := three_neighbors_exhaust hrx.symm hxy hxa hry.ne har hay hdx
  have hNy := three_neighbors_exhaust hry.symm hxy.symm hyb hrx.ne hbr hbx hdy
  obtain ⟨hra,hrb⟩ := punctured_carrier_reaches_root hrx hry hxy hxa hyb hay hNx hNy P hP hrP hnrx hnry hnxy hnab
  have hle : puncture (G.deleteEdges {s(a,b)}) ({x,y} : Set (Fin n)) ≤ puncture G ({x,y} : Set (Fin n)) := by
    intro u v huv
    exact ⟨(deleteEdges_le _) huv.1,huv.2⟩
  exact hfail (cubic_triangle_even_attachment_reduction hsmall hG hrx hry hxy hxa hyb
    har hay hbr hbx hab hNx hNy hrodd haeven (hra.mono hle) (hrb.mono hle))

lemma failure_no_degree_five_short_triangle_cubic_pair {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (r : Fin n) (L : RootedCycleRep T r) {x y : Fin n}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hC : L.cycle=Walk.cons hrx (Walk.cons hxy (Walk.cons hry.symm Walk.nil)))
    (ht : L.tail.length=1 ∨ L.tail.length=2)
    (hd : Nat.card (G.neighborSet r)=5)
    (hdx : Nat.card (G.neighborSet x)=3) (hdy : Nat.card (G.neighborSet y)=3) : False := by
  have hc : L.cycle.length=3 := by rw [hC]; rfl
  have hq := (Erdos583ShortTriangleIncidenceDevelopment.failure_any_short_triangle_root_degree
    hsmall hG hfail T hs hm r L hc (by omega)).1
  have hxC : x ∈ L.cycle.support := by rw [hC]; simp
  have hyC : y ∈ L.cycle.support := by rw [hC]; simp
  obtain ⟨j,hji,P,hP,_,hrP,hdis⟩ := degree_five_two_cubic_carrier T hs hm r L hc ht hq hd
    hxC hyC hrx.ne.symm hry.ne.symm hxy.ne hdx hdy
  have hnot {e : Sym2 (Fin n)} (he : e ∈ L.cycle.toSubgraph.edgeSet) : e ∉ P.edges :=
    fun h ↦ Set.disjoint_left.mp hdis he (P.mem_edges_toSubgraph.mpr h)
  have hnr := hnot (show s(r,x) ∈ L.cycle.toSubgraph.edgeSet by rw [hC]; simp)
  have hny := hnot (show s(r,y) ∈ L.cycle.toSubgraph.edgeSet by rw [hC]; simp [Sym2.eq_swap])
  have hnxy := hnot (show s(x,y) ∈ L.cycle.toSubgraph.edgeSet by rw [hC]; simp)
  have hrodd : Odd (Nat.card (G.neighborSet r)) := by rw [hd]; decide
  exact failure_no_odd_root_cubic_triangle_carrier hsmall hG hfail hrx hry hxy hrodd hdx hdy P hP hrP hnr hny hnxy

end Erdos583CubicTriangleExclusionDevelopment
