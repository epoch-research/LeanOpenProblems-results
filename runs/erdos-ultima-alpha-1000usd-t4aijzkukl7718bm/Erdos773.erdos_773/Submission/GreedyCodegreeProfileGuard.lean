import Submission.GreedyProfileGuard
import Submission.GreedyCodegreePhysicalStep
import Submission.GreedyNonlinearGuardTails

/-!
The nonlinear profile guard has a noncircular availability invariant.
An avoiding path implies a full run; its probability is handled separately.
-/
namespace Erdos773.GreedyCodegreeProfileGuard
open Finset GreedyHypergraphState StoppedGreedyMoments GreedyCommonNeighbors
open GreedyTrackedState GreedyTrackedMoments FiniteKernelCrossing
open GreedyProfileRecords GreedyTrajectoryCalculus GreedyScaledTrajectory GreedyEnvelopeCalculus
open GreedyProfileGuard GreedyCodegreeDrift
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def guard (p : Parameters) (H : Finset (Finset α)) (L T C B2 B3 n : ℕ) (s : Tracked H T) : Prop :=
  Valid H L n s ∧ QBox p H n s.chosen ∧ DegreeBox p H n s.chosen ∧ CommonBox H C s.chosen ∧
  (∀ u ∈ available H s.chosen, duplicateExcess H s.chosen u ≤ C) ∧
  (∀ u ∈ available H s.chosen, promotionDefect H s.chosen 2 u ≤ B2) ∧
  (∀ u ∈ available H s.chosen, promotionDefect H s.chosen 3 u ≤ B3)

def bad (p : Parameters) (H : Finset (Finset α)) (T C B2 B3 n : ℕ) (s : Tracked H T) : Prop :=
  GreedyNonlinearGuardTails.auxiliaryBad H C B2 B3 s.chosen ∨
    ∃ (j : Fin 3) (u : α) (lower : Bool), crossing p H T j u lower n s

/-- The Q box holds at every reachable state whose records are still
    running. Prior guarded steps, not a presumed successful future, imply it. -/
theorem reach_running_QBox {p : Parameters} {H : Finset (Finset α)} 
    (hH : ∀ e ∈ H, e.card = 4) (hV : (Fintype.card α:ℝ) = p.V)
    {L T C B2 B3 n : ℕ} {τ : ℝ} (hh : Horizon p L T C τ) {s : Tracked H T}
    (hs : GreedyTrackedState.Reach H L T (guard p H L T C B2 B3) n s) (hrun : s.running = true) :
    QBox p H n s.chosen := by
  induction hs with
  | initial => exact initial_QBox hH hV hh.bounds.rho_nonneg hh.bounds.V_pos.le
  | @action n s a hs hn ha ih =>
    cases a with
    | none =>
      have hQ := ih hrun
      have hr := ready_of_QBox hh hn.le hQ
      exact ((mem_actions_none H L s.chosen).mp ha hr).elim
    | some w =>
      have hg : s.running = true ∧ guard p H L T C B2 B3 n s := by
        by_contra h
        have hf := (update_guard_failed w h).2.2
        rw [hrun] at hf
        contradiction
      have hw := ((mem_actions_some H L s.chosen w).mp ha).2
      have hd := hg.2.2.2.1 0 w hw
      change |((incident H s.chosen 2 w).card:ℝ)-F2 p.d (time p n)| ≤
        E2 p.d p.rho p.K (time p n) at hd
      have hQ := GreedyCodegreePhysicalStep.availability_box_step hw (hh.conditions hn.le) hg.2.2.1 hd (hg.2.2.2.2.2.1 w hw)
      simpa only [QBox,update_chosen,GreedyFiniteKernel.move,time_step] using hQ

/-- All good reachable running states satisfy the concrete guard. The live
    recorded tubes provide actual degrees only after readiness is justified. -/
theorem good_implies_guard {p : Parameters} {H : Finset (Finset α)} 
    (hH : ∀ e ∈ H, e.card = 4) (hV : (Fintype.card α:ℝ) = p.V)
    (hD : ∀ u : α, (HypergraphDegreeTrim.degree H u:ℝ) = p.d^3)
    {L T C B2 B3 n : ℕ} {τ : ℝ} (hh : Horizon p L T C τ) (hn : n ≤ T) {s : Tracked H T}
    (hs : GreedyTrackedState.Reach H L T (guard p H L T C B2 B3) n s) (hrun : s.running = true)
    (hbad : ¬bad p H T C B2 B3 n s) : guard p H L T C B2 B3 n s := by
  have hQ := reach_running_QBox hH hV hh hs hrun
  have hr := ready_of_QBox hh hn hQ
  have hc := GreedyNonlinearGuardTails.controls_of_not_bad (fun h => hbad (Or.inl h))
  refine ⟨hs.valid,hQ,?_,hc.2.1 s.chosen (Subset.refl _),
    (fun u _ => hc.1 s.chosen (Subset.refl _) u),
    (fun u _ => hc.2.2.1 s.chosen (Subset.refl _) u),
    (fun u _ => hc.2.2.2 s.chosen (Subset.refl _) u)⟩
  intro j u hu
  exact live_tube hH p hD hs.valid hrun hr j u hu
    (fun lower hc => hbad (Or.inr ⟨j,u,lower,hc⟩))

/-- Once an actual avoiding path is established, this guard proves a full
    independent run of T choices, not a cardinality-or-early-stop alternative. -/
theorem full_run_of_goodPath {p : Parameters} {H : Finset (Finset α)} 
    (hH : ∀ e ∈ H, e.card = 4) (hV : (Fintype.card α:ℝ) = p.V)
    (hD : ∀ u : α, (HypergraphDegreeTrim.degree H u:ℝ) = p.d^3)
    {L T C B2 B3 : ℕ} {τ : ℝ} (hh : Horizon p L T C τ)
    (hp : GoodPath (GreedyTrackedState.kernel H L T (guard p H L T C B2 B3))
      (bad p H T C B2 B3) 0 T (initial H T)) :
    ∃ I : Finset α, Independent H I ∧ I.card = T := by
  have hnon : ∀ e ∈ H, e.Nonempty := fun e he => card_pos.mp (by rw [hH e he]; omega)
  obtain ⟨s,hs,hrun,hvalid,hi,hcard,hgood⟩ := goodPath_full_run H hnon L T hh.L_pos
    (guard p H L T C B2 B3) (bad p H T C B2 B3)
    (fun n hn s hs hr hg => good_implies_guard hH hV hD hh hn.le hs hr hg)
    (fun s hs hr _ => ready_of_QBox hh le_rfl (reach_running_QBox hH hV hh hs hr)) hp
  exact ⟨s.chosen,hi,hcard⟩

#print axioms reach_running_QBox
#print axioms good_implies_guard
#print axioms full_run_of_goodPath
end
end Erdos773.GreedyCodegreeProfileGuard
