import Submission.HeptagonCore
import Submission.HeptagonPortCover

/-! A whole seven-cycle is excluded by contracting its four-port dense core. -/
namespace Erdos583HeptagonExclusionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails Erdos583Work.VertexCritical
open Erdos583HeptagonRegionDevelopment Erdos583HeptagonCoreDevelopment
open Erdos583HeptagonPortCoverDevelopment
open scoped Classical
set_option maxHeartbeats 2200000

lemma failure_no_heptagon {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {r : Fin n}
    (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) : False := by
  obtain ⟨j,l,hij,hil,hjl,hjhit,hlhit⟩ := failure_two_carriers hsmall hG hfail T hs hm i C hC hl hi
  have hcore := two_carrier_core_complement_ncard T hs hm i j l hij hil hjl C hC hl hi hjhit hlhit
  have hS : C.toSubgraph.verts.ncard=7 := by rw [Walk.verts_toSubgraph,cycle_support_ncard hC,hl]
  apply hfail
  apply core_reduction hsmall G hG C.toSubgraph.verts hS hcore
  intro x hx
  have hh := two_carrier_degree_formula T hs hm i j l hij hil hjl C hC hl hi hjhit hlhit x
    (C.mem_verts_toSubgraph.mp hx)
  split_ifs at hh <;> omega

lemma whole_cycle_length_ge_eight {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {r : Fin n}
    (C : G.Walk r r) (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph) : 8 ≤ C.length := by
  have hh := HexagonExclusion.whole_cycle_length_ge_seven hsmall hG hfail T hs hm i C hC hi
  by_contra hn
  exact failure_no_heptagon hsmall hG hfail T hs hm i C hC (by omega) hi

end Erdos583HeptagonExclusionDevelopment
