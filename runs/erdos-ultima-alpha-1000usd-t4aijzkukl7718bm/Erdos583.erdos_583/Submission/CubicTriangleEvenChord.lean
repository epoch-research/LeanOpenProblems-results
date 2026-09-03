import Submission.CubicTrianglePuncture

/-! A cubic pair in the short-triangle branch forces an even-even nonbridge. -/
namespace Erdos583CubicTriangleEvenChordDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583CubicTriangleReductionDevelopment Erdos583CubicTriangleCarrierDevelopment
open Erdos583CubicTrianglePunctureDevelopment Erdos583ShortTriangleSingleCarrierDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma failure_cubic_triangle_carrier_even_chord {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {r x y : Fin n} (hrx : G.Adj r x) (hry : G.Adj r y) (hxy : G.Adj x y)
    (hrodd : Odd (Nat.card (G.neighborSet r)))
    (hdx : Nat.card (G.neighborSet x)=3) (hdy : Nat.card (G.neighborSet y)=3)
    (P : G.Walk x y) (hP : P.IsPath) (hrP : r ∈ P.support)
    (hnrx : s(r,x) ∉ P.edges) (hnry : s(r,y) ∉ P.edges) (hnxy : s(x,y) ∉ P.edges) :
    ∃ a b, G.Adj x a ∧ G.Adj y b ∧ a ≠ r ∧ a ≠ y ∧ b ≠ r ∧ b ≠ x ∧ a ≠ b ∧
      G.Adj a b ∧ s(a,b) ∉ P.edges ∧ ¬G.IsBridge s(a,b) ∧
      Even (Nat.card (G.neighborSet a)) ∧ Even (Nat.card (G.neighborSet b)) := by
  obtain ⟨a,b,hxa,hyb,har,hay,hbr,hbx,hab,hNx,hNy,hreach,hnot⟩ :=
    path_between_triangle_vertices_external_data hrx hry hxy hdx hdy P hP hrP hnrx hnry hnxy
  have hedge := failure_cubic_triangle_external_adj hsmall hG hfail hrx hry hxy hxa hyb har hay hbr hbx hab hNx hNy hreach
  have haeven : Even (Nat.card (G.neighborSet a)) := by
    apply Nat.not_odd_iff_even.mp
    intro hao
    exact hfail (cubic_triangle_odd_attachment_reduction hsmall hG hrx hry hxy hxa hyb hedge
      har hay hbr hbx hNx hNy hrodd hao P hP hrP hnrx hnry hnxy hnot)
  have hbeven : Even (Nat.card (G.neighborSet b)) := by
    apply Nat.not_odd_iff_even.mp
    intro hbo
    have hrPr : r ∈ P.reverse.support := by simpa only [Walk.support_reverse,List.mem_reverse] using hrP
    have hn1 : s(r,y) ∉ P.reverse.edges := by simpa only [Walk.edges_reverse,List.mem_reverse] using hnry
    have hn2 : s(r,x) ∉ P.reverse.edges := by simpa only [Walk.edges_reverse,List.mem_reverse] using hnrx
    have hn3 : s(y,x) ∉ P.reverse.edges := by simpa only [Walk.edges_reverse,List.mem_reverse,Sym2.eq_swap (a := y) (b := x)] using hnxy
    have hn4 : s(b,a) ∉ P.reverse.edges := by simpa only [Walk.edges_reverse,List.mem_reverse,Sym2.eq_swap (a := b) (b := a)] using hnot
    exact hfail (cubic_triangle_odd_attachment_reduction hsmall hG hry hrx hxy.symm hyb hxa hedge.symm
      hbr hbx har hay hNy hNx hrodd hbo P.reverse hP.reverse hrPr hn1 hn2 hn3 hn4)
  have hnbridge : ¬G.IsBridge s(a,b) := by
    obtain ⟨hra,hrb⟩ := punctured_carrier_reaches_root hrx hry hxy hxa hyb hay hNx hNy P hP hrP hnrx hnry hnxy hnot
    intro hb
    exact (isBridge_iff.mp hb).2 ((hra.symm.trans hrb).mono (puncture_le _ _))
  exact ⟨a,b,hxa,hyb,har,hay,hbr,hbx,hab,hedge,hnot,hnbridge,haeven,hbeven⟩

lemma failure_degree_five_short_triangle_even_chord {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
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
    (hdx : Nat.card (G.neighborSet x)=3) (hdy : Nat.card (G.neighborSet y)=3) :
    ∃ a b, G.Adj x a ∧ G.Adj y b ∧ a ≠ r ∧ a ≠ y ∧ b ≠ r ∧ b ≠ x ∧ a ≠ b ∧
      G.Adj a b ∧ ¬G.IsBridge s(a,b) ∧
      Even (Nat.card (G.neighborSet a)) ∧ Even (Nat.card (G.neighborSet b)) := by
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
  obtain ⟨a,b,hxa,hyb,har,hay,hbr,hbx,hab,hedge,_,hnb,hae,hbe⟩ :=
    failure_cubic_triangle_carrier_even_chord hsmall hG hfail hrx hry hxy hrodd hdx hdy P hP hrP hnr hny hnxy
  exact ⟨a,b,hxa,hyb,har,hay,hbr,hbx,hab,hedge,hnb,hae,hbe⟩

end Erdos583CubicTriangleEvenChordDevelopment
