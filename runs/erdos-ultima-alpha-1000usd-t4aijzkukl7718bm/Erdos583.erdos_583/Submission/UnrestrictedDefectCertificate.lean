import Submission.FreeRootWholeCycleExclusion
import Submission.JointTailCarrier

/-! Compatible unrestricted-cycle and free-tail optima in a one-defect failure. -/
namespace Erdos583UnrestrictedDefectCertificateDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583Work.LollipopEar Erdos583Work.CarrierCount Erdos583Work.CarrierLength
open Erdos583FreeRootCycleMinimumDevelopment Erdos583FreeRootWholeCycleExclusionDevelopment
open Erdos583JointTailCarrierDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma exists_unrestricted_cycle_tail_carrier_optimum {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (r : V)
    (hs : T.score+1=G.edgeSet.ncard+k) (hr : HasRoot T r) :
    ∃ U : TrailFamily G k, ∃ s : V, ∃ L : RootedCycleRep U s,
      U.score=T.score ∧
      (∀ W : TrailFamily G k, ∀ t : V, ∀ M : RootedCycleRep W t,
        W.score=U.score → L.cycle.length ≤ M.cycle.length) ∧
      (∀ W : TrailFamily G k, ∀ M : RootedCycleRep W s,
        W.score=U.score → M.cycle=L.cycle → L.tail.length ≤ M.tail.length) ∧
      (∀ W : TrailFamily G k, W.score=U.score →
        (W.walk L.index).toSubgraph=(U.walk L.index).toSubgraph →
        carrierCount W (U.walk L.index).toSubgraph.verts ≤ carrierCount U (U.walk L.index).toSubgraph.verts) ∧
      (∀ W : TrailFamily G k, W.score=U.score →
        (W.walk L.index).toSubgraph=(U.walk L.index).toSubgraph →
        carrierCount W (U.walk L.index).toSubgraph.verts=carrierCount U (U.walk L.index).toSubgraph.verts →
        carrierLength U (U.walk L.index).toSubgraph.verts ≤ carrierLength W (U.walk L.index).toSubgraph.verts) := by
  obtain ⟨R,s,N,hRs,hC⟩ := exists_unrestricted_shortest_cycle T r hs hr
  obtain ⟨U,L,hUs,hLC,hTail,hMax,hMin⟩ := exists_joint_optimum R s N
  refine ⟨U,s,L,hUs.trans hRs,?_,hTail,hMax,hMin⟩
  intro W t M hWs
  rw [hLC]
  exact hC W t M (hWs.trans hUs)

lemma rooted_cycle_budget_ge_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (T : TrailFamily G k) (r : V) (L : RootedCycleRep T r)
    (hb : Fintype.card V ≤ 2*k) : 2 ≤ k := by
  have hlen : L.cycle.length ≤ Fintype.card V := by
    have hh : L.cycle.toSubgraph.verts.ncard ≤ Fintype.card V := by
      simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card L.cycle.toSubgraph.verts
    rwa [Walk.verts_toSubgraph,cycle_support_ncard L.isCycle] at hh
  have hh := L.isCycle.three_le_length
  omega

lemma failure_has_unrestricted_open_defect {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.Connected ∧
      (¬∃ D : Finset H.Subgraph, GoodDecomposition H D ∧
        D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊) ∧
      ∃ T : TrailFamily H ⌈(Fintype.card V : ℚ)/2⌉₊, ∃ r : V, ∃ L : RootedCycleRep T r,
        T.score+1=H.edgeSet.ncard+⌈(Fintype.card V : ℚ)/2⌉₊ ∧
        (∀ U : TrailFamily H ⌈(Fintype.card V : ℚ)/2⌉₊, U.score ≤ T.score) ∧
        ¬L.tail.Nil ∧
        (∀ W : TrailFamily H ⌈(Fintype.card V : ℚ)/2⌉₊, ∀ t : V, ∀ M : RootedCycleRep W t,
          W.score=T.score → L.cycle.length ≤ M.cycle.length) ∧
        (∀ W : TrailFamily H ⌈(Fintype.card V : ℚ)/2⌉₊, ∀ M : RootedCycleRep W r,
          W.score=T.score → M.cycle=L.cycle → L.tail.length ≤ M.tail.length) := by
  obtain ⟨H,hHG,hH,hfailH,r,R,hs,hr,hm⟩ := EdgeDefect.failure_has_rooted_one_defect G hG hfail
  obtain ⟨T,s,L,hTs,hC,hTail,_,_⟩ := exists_unrestricted_cycle_tail_carrier_optimum R r hs hr
  have hsT : T.score+1=H.edgeSet.ncard+⌈(Fintype.card V : ℚ)/2⌉₊ := by omega
  have hmT (U : TrailFamily H ⌈(Fintype.card V : ℚ)/2⌉₊) : U.score ≤ T.score := by
    rw [hTs]; exact hm U
  have hb : Fintype.card V ≤ 2*⌈(Fintype.card V : ℚ)/2⌉₊ := by
    have hh := Nat.le_ceil ((Fintype.card V : ℚ)/2)
    exact_mod_cast (show (Fintype.card V : ℚ) ≤ 2*(⌈(Fintype.card V : ℚ)/2⌉₊ : ℚ) by linarith)
  exact ⟨H,hHG,hH,hfailH,T,s,L,hsT,hmT,
    unrestricted_minimum_tail_not_nil hH (rooted_cycle_budget_ge_two T s L hb) T hsT hmT s L hC,
    hC,hTail⟩

end Erdos583UnrestrictedDefectCertificateDevelopment
