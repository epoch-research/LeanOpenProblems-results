import Submission.GreedyProfileRecords

/-!
A concrete profile guard and its noncircular Q invariant. Avoiding all
recorded profile crossings and the monotone common-neighbor event is enough
to keep the guard alive and to exclude early stopping. Probability bounds
for that simultaneous avoidance are a separate obligation.
-/
namespace Erdos773.GreedyProfileGuard
open Finset GreedyHypergraphState StoppedGreedyMoments GreedyLinearDrift GreedyCommonNeighbors
open GreedyTrackedState GreedyTrackedMoments FiniteKernelCrossing
open GreedyProfileRecords GreedyTrajectoryCalculus GreedyScaledTrajectory GreedyEnvelopeCalculus
open GreedyUniformHorizon GreedyPhysicalStep
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

structure Horizon (p : Parameters) (L T C : ℕ) (τ : ℝ) : Prop where
  bounds : Bounds p.V p.d p.rho p.K τ C
  time_bound : time p T ≤ τ
  L_pos : 0 < L
  L_upper : (L:ℝ) ≤ (3/4)*p.V*q τ

lemma Horizon.conditions {p : Parameters} {L T C n : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (hn : n ≤ T) : Conditions p.V p.d p.rho p.K (time p n) C := by
  have hd : 0 ≤ p.d := by linarith only [hh.bounds.d_one_le]
  exact GreedyUniformHorizon.conditions hh.bounds (time_nonneg hd hh.bounds.V_pos.le n)
    ((time_mono hd hh.bounds.V_pos.le hn).trans hh.time_bound)

lemma Horizon.rho_pos {p : Parameters} {L T C : ℕ} {τ : ℝ} (hh : Horizon p L T C τ) : 0 < p.rho := by
  by_contra! hn
  have hd : 0 ≤ p.d := by linarith only [hh.bounds.d_one_le]
  have hm := mul_nonpos_of_nonneg_of_nonpos hd hn
  have hc : (0:ℝ) ≤ C := by positivity
  linarith only [hh.bounds.common_bound,hm,hc]

def QBox (p : Parameters) (H : Finset (Finset α)) (n : ℕ) (I : Finset α) : Prop :=
  |((available H I).card:ℝ)-Q p.V (time p n)| ≤ EQ p.V p.rho p.K (time p n)

def DegreeBox (p : Parameters) (H : Finset (Finset α)) (n : ℕ) (I : Finset α) : Prop :=
  ∀ j : Fin 3, ∀ u ∈ available H I,
    |((incident H I (j.val+2) u).card:ℝ)-center p j n| ≤ width p j n

def CommonBox (H : Finset (Finset α)) (C : ℕ) (I : Finset α) : Prop :=
  ∀ u ∈ available H I, ∀ v ∈ available H I, u ≠ v → commonDegree H I u v ≤ C

def guard (p : Parameters) (H : Finset (Finset α)) (L T C n : ℕ) (s : Tracked H T) : Prop :=
  Valid H L n s ∧ QBox p H n s.chosen ∧ DegreeBox p H n s.chosen ∧ CommonBox H C s.chosen

/-- The auxiliary bad event is monotone in the selected carrier. -/
def auxiliaryBad (H : Finset (Finset α)) (C : ℕ) (I : Finset α) : Prop :=
  ∃ u v : α, u ≠ v ∧ GreedyCommonNeighbors.prefixBad H u v C I

lemma auxiliaryBad_mono (H : Finset (Finset α)) (C : ℕ) {I J : Finset α} (hIJ : I ⊆ J) :
    auxiliaryBad H C I → auxiliaryBad H C J := by
  rintro ⟨u,v,huv,S,hSI,hu,hv,hC⟩
  exact ⟨u,v,huv,S,hSI.trans hIJ,hu,hv,hC⟩

lemma commonBox_of_not_auxiliary {H : Finset (Finset α)} {C : ℕ} {I : Finset α}
    (h : ¬auxiliaryBad H C I) : CommonBox H C I := by
  intro u hu v hv huv
  by_contra! hc
  exact h ⟨u,v,huv,I,Subset.refl I,hu,hv,hc⟩

def bad (p : Parameters) (H : Finset (Finset α)) (T C n : ℕ) (s : Tracked H T) : Prop :=
  auxiliaryBad H C s.chosen ∨ ∃ (j : Fin 3) (u : α) (lower : Bool), crossing p H T j u lower n s

lemma ready_of_QBox {p : Parameters} {H : Finset (Finset α)} {L T C n : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (hn : n ≤ T) {I : Finset α} (hQ : QBox p H n I) : Ready H L I := by
  have hc := hh.conditions hn
  have htl : time p n ≤ τ :=
    (time_mono (by linarith only [hh.bounds.d_one_le]) hh.bounds.V_pos.le hn).trans hh.time_bound
  have hq := q_antitone hc.time_nonneg htl
  have hprof := mul_le_mul_of_nonneg_left hq hh.bounds.V_pos.le
  have hactual := (abs_le.mp hQ).1
  have hL : (L:ℝ) ≤ ((available H I).card:ℝ) := by
    dsimp [Q] at hactual
    have hsmall := hc.Q_small
    dsimp [Q] at hsmall
    linarith only [hh.L_upper,hprof,hactual,hsmall]
  apply (ready_iff H L hh.L_pos I).mpr
  exact_mod_cast hL

lemma initial_QBox {p : Parameters} {H : Finset (Finset α)}
    (hH : ∀ e ∈ H, e.card = 4) (hV : (Fintype.card α:ℝ) = p.V) (hρ : 0 ≤ p.rho)
    (hVp : 0 ≤ p.V) : QBox p H 0 ∅ := by
  have hA := available_empty (fun e he => by rw [hH e he]; omega)
  simp only [QBox,time_zero,hA,card_univ,hV,Q,q,pow_succ,mul_zero,neg_zero,Real.exp_zero,mul_one,sub_self,abs_zero]
  dsimp [EQ,budgetWeight]
  have hh := growth_pos p.K 0 0
  positivity

/-- The Q box holds at every reachable state whose records are still
    running. Prior guarded steps, not a presumed successful future, imply it. -/
theorem reach_running_QBox {p : Parameters} {H : Finset (Finset α)} (hlin : Linear H)
    (hH : ∀ e ∈ H, e.card = 4) (hV : (Fintype.card α:ℝ) = p.V)
    {L T C n : ℕ} {τ : ℝ} (hh : Horizon p L T C τ) {s : Tracked H T}
    (hs : GreedyTrackedState.Reach H L T (guard p H L T C) n s) (hrun : s.running = true) :
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
      have hg : s.running = true ∧ guard p H L T C n s := by
        by_contra h
        have hf := (update_guard_failed w h).2.2
        rw [hrun] at hf
        contradiction
      have hw := ((mem_actions_some H L s.chosen w).mp ha).2
      have hd := hg.2.2.2.1 0 w hw
      change |((incident H s.chosen 2 w).card:ℝ)-F2 p.d (time p n)| ≤
        E2 p.d p.rho p.K (time p n) at hd
      have hQ := availability_box_step hlin hw (hh.conditions hn.le) hg.2.2.1 hd
      simpa only [QBox,update_chosen,GreedyFiniteKernel.move,time_step] using hQ

/-- All good reachable running states satisfy the concrete guard. The live
    recorded tubes provide actual degrees only after readiness is justified. -/
theorem good_implies_guard {p : Parameters} {H : Finset (Finset α)} (hlin : Linear H)
    (hH : ∀ e ∈ H, e.card = 4) (hV : (Fintype.card α:ℝ) = p.V)
    (hD : ∀ u : α, (HypergraphDegreeTrim.degree H u:ℝ) = p.d^3)
    {L T C n : ℕ} {τ : ℝ} (hh : Horizon p L T C τ) (hn : n ≤ T) {s : Tracked H T}
    (hs : GreedyTrackedState.Reach H L T (guard p H L T C) n s) (hrun : s.running = true)
    (hbad : ¬bad p H T C n s) : guard p H L T C n s := by
  have hQ := reach_running_QBox hlin hH hV hh hs hrun
  have hr := ready_of_QBox hh hn hQ
  refine ⟨hs.valid,hQ,?_,commonBox_of_not_auxiliary (fun h => hbad (Or.inl h))⟩
  intro j u hu
  exact live_tube hH p hD hs.valid hrun hr j u hu
    (fun lower hc => hbad (Or.inr ⟨j,u,lower,hc⟩))

/-- Once an actual avoiding path is established, this guard proves a full
    independent run of T choices, not a cardinality-or-early-stop alternative. -/
theorem full_run_of_goodPath {p : Parameters} {H : Finset (Finset α)} (hlin : Linear H)
    (hH : ∀ e ∈ H, e.card = 4) (hV : (Fintype.card α:ℝ) = p.V)
    (hD : ∀ u : α, (HypergraphDegreeTrim.degree H u:ℝ) = p.d^3)
    {L T C : ℕ} {τ : ℝ} (hh : Horizon p L T C τ)
    (hp : GoodPath (GreedyTrackedState.kernel H L T (guard p H L T C))
      (bad p H T C) 0 T (initial H T)) :
    ∃ I : Finset α, Independent H I ∧ I.card = T := by
  have hnon : ∀ e ∈ H, e.Nonempty := fun e he => card_pos.mp (by rw [hH e he]; omega)
  obtain ⟨s,hs,hrun,hvalid,hi,hcard,hgood⟩ := goodPath_full_run H hnon L T hh.L_pos
    (guard p H L T C) (bad p H T C)
    (fun n hn s hs hr hg => good_implies_guard hlin hH hV hD hh hn.le hs hr hg)
    (fun s hs hr _ => ready_of_QBox hh le_rfl (reach_running_QBox hlin hH hV hh hs hr)) hp
  exact ⟨s.chosen,hi,hcard⟩

#print axioms ready_of_QBox
#print axioms reach_running_QBox
#print axioms good_implies_guard
#print axioms full_run_of_goodPath
end
end Erdos773.GreedyProfileGuard
