import Submission.ShortTriangleComponents
import Submission.UnrestrictedDefectCertificate

/-! Degree and length consequences at an unrestricted minimum with triangular cycle. -/
namespace Erdos583ShortTriangleBoundsDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583ShortTriangleRootExclusionDevelopment Erdos583RootEndpointTailCapacityDevelopment
open Erdos583FreeRootWholeCycleExclusionDevelopment Erdos583UnrestrictedDefectCertificateDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma failure_short_triangle_root_degree {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (r : Fin n) (L : RootedCycleRep T r)
    (hmin : ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ u : Fin n, ∀ M : RootedCycleRep W u,
      W.score=T.score → L.cycle.length ≤ M.cycle.length)
    (hcycle : L.cycle.length=3) (htail : L.tail.length ≤ 2) :
    T.quota r=1 ∧ Odd (Nat.card (G.neighborSet r)) ∧ 5 ≤ Nat.card (G.neighborSet r) := by
  have hb : Fintype.card (Fin n) ≤ 2*⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    simp only [Fintype.card_fin,BridgeGlue.ceil_half]; omega
  have hn := unrestricted_minimum_tail_not_nil hG (rooted_cycle_budget_ge_two T r L hb) T hs hm r L hmin
  have hpos : 0 < L.tail.length := Walk.not_nil_iff_lt_length.mp hn
  have hq : T.quota r=1 := by
    rcases (show L.tail.length=1 ∨ L.tail.length=2 by omega) with hl | hl
    · exact minimum_one_edge_tail_root_quota_one T hs hm r L hmin hl
    · exact failure_two_tail_triangle_root_quota_one hsmall hG hfail T hs hm r L hmin hcycle hl
  have ho : Odd (Nat.card (G.neighborSet r)) := (QuotaParity.quota_odd_iff T r).mp (by rw [hq]; decide)
  have hge : 3 ≤ Nat.card (G.neighborSet r) := by
    have hh : ((T.walk L.index).toSubgraph.neighborSet r).ncard ≤ (G.neighborSet r).ncard :=
      Set.ncard_le_ncard (fun _ h ↦ (T.walk L.index).toSubgraph.adj_sub h)
    rw [FreeTailGroups.open_rooted_member_degree T r L hn] at hh
    exact hh
  have hne : Nat.card (G.neighborSet r) ≠ 3 := by
    intro he
    have hh := TriangleTailTwo.cubic_triangle_tail_length_ge_three hsmall hG hfail T r L hs hm he (by omega) hcycle
    omega
  obtain ⟨m,hm⟩ := ho
  exact ⟨hq,⟨m,hm⟩,by omega⟩

lemma failure_even_root_triangle_tail_length_ge_three {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (r : Fin n) (L : RootedCycleRep T r)
    (hmin : ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ u : Fin n, ∀ M : RootedCycleRep W u,
      W.score=T.score → L.cycle.length ≤ M.cycle.length)
    (hcycle : L.cycle.length=3) (he : Even (Nat.card (G.neighborSet r))) : 3 ≤ L.tail.length := by
  by_contra hlen
  have ho := (failure_short_triangle_root_degree hsmall hG hfail T hs hm r L hmin hcycle (by omega)).2.1
  exact (Nat.not_even_iff_odd.mpr ho) he

end Erdos583ShortTriangleBoundsDevelopment
