import Submission.UnifiedMinimalDefect

/-! A compatible stronger tail optimum. The tail comparison now ranges over
all roots and all cycles of the minimum length. No energy minimum is added,
and no assertion is made that this certificate is impossible. -/
namespace Erdos583GlobalTailDefectDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583Work.LollipopEar Erdos583Work.CarrierCount Erdos583Work.CarrierLength
open Erdos583FreeRootCycleMinimumDevelopment Erdos583JointTailCarrierDevelopment
open Erdos583UnifiedMinimalDefectDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma exists_global_cycle_tail_carrier_optimum {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (r : V)
    (hs : T.score+1=G.edgeSet.ncard+k) (hr : HasRoot T r) :
    ∃ U : TrailFamily G k, ∃ s : V, ∃ M : RootedCycleRep U s,
      U.score=T.score ∧
      (∀ W : TrailFamily G k, ∀ t : V, ∀ N : RootedCycleRep W t,
        W.score=U.score → M.cycle.length ≤ N.cycle.length) ∧
      (∀ W : TrailFamily G k, ∀ t : V, ∀ N : RootedCycleRep W t,
        W.score=U.score → N.cycle.length=M.cycle.length → M.tail.length ≤ N.tail.length) ∧
      (∀ W : TrailFamily G k, ∀ N : RootedCycleRep W s,
        W.score=U.score → N.cycle=M.cycle → M.tail.length ≤ N.tail.length) ∧
      (∀ W : TrailFamily G k, W.score=U.score →
        (W.walk M.index).toSubgraph=(U.walk M.index).toSubgraph →
        carrierCount W (U.walk M.index).toSubgraph.verts ≤
          carrierCount U (U.walk M.index).toSubgraph.verts) ∧
      (∀ W : TrailFamily G k, W.score=U.score →
        (W.walk M.index).toSubgraph=(U.walk M.index).toSubgraph →
        carrierCount W (U.walk M.index).toSubgraph.verts=
          carrierCount U (U.walk M.index).toSubgraph.verts →
        carrierLength U (U.walk M.index).toSubgraph.verts ≤
          carrierLength W (U.walk M.index).toSubgraph.verts) := by
  obtain ⟨R,a,L,hRs,hC⟩ := exists_unrestricted_shortest_cycle T r hs hr
  let P (m : ℕ) := ∃ S : TrailFamily G k, ∃ b : V, ∃ N : RootedCycleRep S b,
    S.score=R.score ∧ N.cycle.length=L.cycle.length ∧ N.tail.length=m
  have hex : ∃ m, P m := ⟨L.tail.length,R,a,L,rfl,rfl,rfl⟩
  obtain ⟨S,b,N,hSs,hNC,hNT⟩ := Nat.find_spec hex
  have hGlobal (W : TrailFamily G k) (t : V) (Q : RootedCycleRep W t)
      (hWs : W.score=S.score) (hQC : Q.cycle.length=N.cycle.length) :
      N.tail.length ≤ Q.tail.length := by
    rw [hNT]
    exact Nat.find_min' hex ⟨W,t,Q,hWs.trans hSs,hQC.trans hNC,rfl⟩
  obtain ⟨U,M,hUs,hMC,hTail,hMax,hMin⟩ := exists_joint_optimum S b N
  have hMT : M.tail.length=N.tail.length := by
    apply Nat.le_antisymm
    · exact hTail S N hUs.symm hMC.symm
    · exact hGlobal U b M hUs (congrArg Walk.length hMC)
  refine ⟨U,b,M,hUs.trans (hSs.trans hRs),?_,?_,hTail,hMax,hMin⟩
  · intro W t Q hWs
    rw [hMC,hNC]
    exact hC W t Q (hWs.trans (hUs.trans hSs))
  · intro W t Q hWs hQC
    rw [hMT]
    exact hGlobal W t Q (hWs.trans hUs) (hQC.trans (congrArg Walk.length hMC))

/-- The old optimized defect, with a genuinely compatible stronger comparison
of tails. The original certificate is available through `toOptimizedDefect`. -/
structure GloballyTailOptimized {n : ℕ} (G : SimpleGraph (Fin n)) extends OptimizedDefect G where
  global_tail_minimum : ∀ U : TrailFamily G (budget n), ∀ s : Fin n,
    ∀ M : RootedCycleRep U s, U.score=family.score →
      M.cycle.length=rep.cycle.length → rep.tail.length ≤ M.tail.length

lemma minimal_failure_has_global_tail_optimum (F : MinimalFailure) :
    Nonempty (GloballyTailOptimized F.graph) := by
  obtain ⟨D⟩ := F.has_optimized_defect
  obtain ⟨U,s,M,hUs,hC,hGlobal,hTail,hMax,hMin⟩ :=
    exists_global_cycle_tail_carrier_optimum D.family D.root D.score D.rep.hasRoot
  exact ⟨{
    family := U
    root := s
    rep := M
    score := by rw [hUs]; exact D.score
    maximum := fun W ↦ by rw [hUs]; exact D.maximum W
    cycle_minimum := hC
    tail_minimum := hTail
    carrier_maximum := hMax
    carrier_minimum := hMin
    global_tail_minimum := hGlobal
  }⟩

lemma failure_has_global_tail_certificate {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected)
    (hf : ¬∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      E.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊) :
    ∃ F : MinimalFailure, Nonempty (GloballyTailOptimized F.graph) := by
  obtain ⟨F,_⟩ := failure_has_unified_certificate G hG hf
  exact ⟨F,minimal_failure_has_global_tail_optimum F⟩

lemma GloballyTailOptimized.anchor_length_le_of_cycle_le {n : ℕ}
    {G : SimpleGraph (Fin n)} (D : GloballyTailOptimized G)
    (U : TrailFamily G (budget n)) (s : Fin n) (M : RootedCycleRep U s)
    (hs : U.score=D.family.score) (hC : M.cycle.length ≤ D.rep.cycle.length) :
    D.rep.cycle.length+D.rep.tail.length ≤ M.cycle.length+M.tail.length := by
  have he := hC.antisymm (D.cycle_minimum U s M hs)
  have ht := D.global_tail_minimum U s M hs he
  omega

lemma GloballyTailOptimized.no_shorter_tail_at_minimum_cycle {n : ℕ}
    {G : SimpleGraph (Fin n)} (D : GloballyTailOptimized G)
    (U : TrailFamily G (budget n)) (s : Fin n) (M : RootedCycleRep U s)
    (hs : U.score=D.family.score) (hT : M.tail.length < D.rep.tail.length) :
    D.rep.cycle.length < M.cycle.length := by
  by_contra hn
  have he := Nat.le_antisymm (by omega) (D.cycle_minimum U s M hs)
  have ht := D.global_tail_minimum U s M hs he
  omega

end Erdos583GlobalTailDefectDevelopment
