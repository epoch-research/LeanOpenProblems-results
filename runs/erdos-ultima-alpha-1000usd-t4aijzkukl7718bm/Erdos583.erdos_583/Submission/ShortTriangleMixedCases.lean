import Submission.DegreeTwoNeighborFive

/-! Only cubic/quartic and quartic/quartic nonroot pairs remain at a degree-five short triangle. -/
namespace Erdos583ShortTriangleMixedCasesDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583ShortTriangleIncidenceDevelopment Erdos583ShortTriangleDegreeFourDevelopment
open Erdos583DegreeTwoNeighborFiveDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma failure_degree_five_short_triangle_nonroot_degrees {n : ℕ}
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
    3 ≤ Nat.card (G.neighborSet x) ∧ 3 ≤ Nat.card (G.neighborSet y) ∧
      Nat.card (G.neighborSet x)+T.quota x=4 ∧ Nat.card (G.neighborSet y)+T.quota y=4 := by
  have hc : L.cycle.length=3 := by rw [hC]; rfl
  have hxC : x ∈ L.cycle.support := by rw [hC]; simp
  have hyC : y ∈ L.cycle.support := by rw [hC]; simp
  have hxb := failure_short_triangle_other_cycle_degree hsmall hG hfail T hs hm r L hc ht hxC hrx.ne.symm
  have hyb := failure_short_triangle_other_cycle_degree hsmall hG hfail T hs hm r L hc ht hyC hry.ne.symm
  rw [hd] at hxb hyb
  have hx2 : 2 ≤ Nat.card (G.neighborSet x) := by
    have hh := Set.ncard_mono (show ({r,y} : Set (Fin n)) ⊆ G.neighborSet x by
      rintro v (rfl|rfl); exact hrx.symm; exact hxy)
    simpa only [Set.ncard_pair hry.ne,←Nat.card_coe_set_eq] using hh
  have hy2 : 2 ≤ Nat.card (G.neighborSet y) := by
    have hh := Set.ncard_mono (show ({r,x} : Set (Fin n)) ⊆ G.neighborSet y by
      rintro v (rfl|rfl); exact hry.symm; exact hxy.symm)
    simpa only [Set.ncard_pair hrx.ne,←Nat.card_coe_set_eq] using hh
  have hx3 : 3 ≤ Nat.card (G.neighborSet x) := by
    by_contra hn
    have hh := degree_two_neighbors_ge_five hsmall hG hfail hxy (by omega)
    omega
  have hy3 : 3 ≤ Nat.card (G.neighborSet y) := by
    by_contra hn
    have hh := degree_two_neighbors_ge_five hsmall hG hfail hxy.symm (by omega)
    omega
  have hquota (v : Fin n) (hlo : 3 ≤ Nat.card (G.neighborSet v))
      (hhi : Nat.card (G.neighborSet v)+T.quota v+1 ≤ 5) :
      Nat.card (G.neighborSet v)+T.quota v=4 := by
    by_cases he : Nat.card (G.neighborSet v)=4
    · omega
    have he : Nat.card (G.neighborSet v)=3 := by omega
    have ho : Odd (T.quota v) := (QuotaParity.quota_odd_iff T v).mpr (by rw [he]; decide)
    have hp := ho.pos
    omega
  exact ⟨hx3,hy3,hquota x hx3 hxb,hquota y hy3 hyb⟩

lemma failure_degree_five_short_triangle_pair_cases {n : ℕ}
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
    (Nat.card (G.neighborSet x)=4 ∧ Nat.card (G.neighborSet y)=3) ∨
      (Nat.card (G.neighborSet x)=3 ∧ Nat.card (G.neighborSet y)=4) ∨
      (Nat.card (G.neighborSet x)=4 ∧ Nat.card (G.neighborSet y)=4) := by
  obtain ⟨hx,hy,hqx,hqy⟩ := failure_degree_five_short_triangle_nonroot_degrees
    hsmall hG hfail T hs hm r L hrx hxy hry hC ht hd
  have hh := failure_degree_five_short_triangle_has_degree_four hsmall hG hfail T hs hm r L
    hrx hxy hry hC ht hd
  omega

end Erdos583ShortTriangleMixedCasesDevelopment
