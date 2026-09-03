import Submission.Work
import Submission.HexagonCarriers

/-! Whole six-cycles are excluded from smallest-order failures. -/
namespace Erdos583HexagonExclusionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails Erdos583Work.VertexCritical
open Erdos583Work.BridgeGlue Erdos583Work.PentagonExclusion
open Erdos583Work.CarrierCount Erdos583Work.CarrierLength Erdos583Work.CarrierGroups
open Erdos583HexagonCarriersDevelopment Erdos583HexagonExcursionDevelopment
open scoped Classical
set_option maxHeartbeats 1800000

lemma failure_no_whole_hexagon {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {r : Fin n}
    (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=6)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) : False := by
  have hn := Set.ncard_le_card C.toSubgraph.verts
  rw [Walk.verts_toSubgraph,cycle_support_ncard hC,hl,Nat.card_fin] at hn
  have hk : 2 ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    simp only [Fintype.card_fin,ceil_half]; omega
  obtain ⟨j,hij,hhit⟩ := exists_normal_carrier T hG hk i C hi
  obtain ⟨a,b,A,P,B,hj,hP,hPv,hPl,hA,hB⟩ := maximum_carrier_contiguous T hs hm i j hij C hC hl hi hhit
  apply ContiguousRegion.failure_no_single_contiguous_member hsmall hG hfail T hs hm i j hij C hC hi A P B hj
  · intro hn
    have he := Walk.nil_iff_length_eq.mp hn
    omega
  · exact hA
  · exact hB
  · intro x hx
    rw [←Walk.mem_verts_toSubgraph,hPv] at hx
    exact C.mem_verts_toSubgraph.mp hx
  · intro l hli hlj x hx hxC
    exact hlj (carrier_unique T hs hm i l j hli.symm hij C hC hl hi ⟨x,hx,hxC⟩ hhit)

lemma whole_cycle_length_ge_seven {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {r : Fin n}
    (C : G.Walk r r) (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph) :
    7 ≤ C.length := by
  have hl := whole_cycle_length_ge_six hsmall hG hfail T hs hm i C hC hi
  have hne : C.length ≠ 6 := fun he ↦ failure_no_whole_hexagon hsmall hG hfail T hs hm i C hC he hi
  omega

lemma optimized_cycle_has_two_carriers {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {r : Fin n} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hmax : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=C.toSubgraph → PreservesIncidence T U C.toSubgraph.verts →
      carrierCount U C.toSubgraph.verts ≤ carrierCount T C.toSubgraph.verts)
    (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
      (U.walk i).toSubgraph=C.toSubgraph → PreservesIncidence T U C.toSubgraph.verts →
      carrierCount U C.toSubgraph.verts=carrierCount T C.toSubgraph.verts →
      carrierLength T C.toSubgraph.verts ≤ carrierLength U C.toSubgraph.verts) :
    2 ≤ (carrierIndices T i C.toSubgraph.verts).card := by
  have hlo := whole_cycle_length_ge_seven hsmall hG hfail T hs hm i C hC hi
  have hhi := (OutsideCarrierBudget.optimized_cycle_length_bound hsmall hG hfail T hs i C hC hi hmax hmin).1
  omega

end Erdos583HexagonExclusionDevelopment
