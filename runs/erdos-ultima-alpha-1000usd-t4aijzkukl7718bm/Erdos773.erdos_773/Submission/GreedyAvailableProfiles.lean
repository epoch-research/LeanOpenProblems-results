import Submission.GreedyTrackedState

/-!
Deterministic tracking of the available cardinality from uniform local
2-degree profiles in a linear hypergraph. A choice removes exactly one
chosen vertex and its d_2 neighbors. No separate Q concentration theorem
is needed for this implication. The degree profile bounds are hypotheses.
-/
namespace Erdos773.GreedyAvailableProfiles
open Finset GreedyHypergraphState StoppedGreedyMoments
open FiniteKernelCrossing GreedyTrackedState GreedyLinearDrift
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The deterministic remaining-availability profile associated to a
    bound on each chosen vertex's two-degree. -/
def remaining (H : Finset (Finset α)) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (available H ∅).card-∑ k ∈ range n, (1+f k)

@[simp] lemma remaining_zero (H : Finset (Finset α)) (f : ℕ → ℝ) :
    remaining H f 0 = (available H ∅).card := by simp [remaining]

lemma remaining_step (H : Finset (Finset α)) (f : ℕ → ℝ) (n : ℕ) :
    remaining H f (n+1) = remaining H f n-1-f n := by
  simp only [remaining,sum_range_succ]
  ring

lemma remaining_antitone {H : Finset (Finset α)} {f : ℕ → ℝ} {T n m : ℕ}
    (hf : ∀ k < T, 0 ≤ 1+f k) (hnm : n ≤ m) (hmT : m ≤ T) :
    remaining H f m ≤ remaining H f n := by
  apply sub_le_sub_left
  apply sum_le_sum_of_subset_of_nonneg (range_mono hnm)
  intro k hk hkn
  exact hf k (lt_of_lt_of_le (mem_range.mp hk) hmT)

/-- A terminal lower-availability budget implies all earlier budgets when
    the proposed per-step losses are nonnegative. -/
lemma remaining_budget {H : Finset (Finset α)} {f : ℕ → ℝ} {L T : ℕ}
    (hf : ∀ k < T, 0 ≤ 1+f k) (hT : (L:ℝ) ≤ remaining H f T) :
    ∀ n ≤ T, (L:ℝ) ≤ remaining H f n := by
  intro n hn
  exact hT.trans (remaining_antitone hf hn le_rfl)

/-- A profile defined by discrete differences telescopes exactly. This
    avoids a Riemann-sum error in availability tracking. -/
theorem remaining_discrete (H : Finset (Finset α)) (q e : ℕ → ℝ) (n : ℕ) :
    remaining H (fun k => q k-q (k+1)-1+e k) n =
      (available H ∅).card-q 0+q n-∑ k ∈ range n, e k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [remaining_step,ih,sum_range_succ]
    ring

/-- A uniform envelope around the discrete profile costs at most T*E in
    the terminal availability budget. No probabilistic estimate is used. -/
lemma remaining_discrete_lower (H : Finset (Finset α)) (q e : ℕ → ℝ)
    (T : ℕ) (E : ℝ) (hq : q 0 = (available H ∅).card)
    (he : ∀ k < T, e k ≤ E) :
    q T-T*E ≤ remaining H (fun k => q k-q (k+1)-1+e k) T := by
  rw [remaining_discrete,← hq,sub_self,zero_add]
  apply sub_le_sub_left
  calc
    _ ≤ ∑ _k ∈ range T, E := sum_le_sum (fun k hk => he k (mem_range.mp hk))
    _ = _ := by simp

/-- In a linear hypergraph the actual availability decrement is 1+d_2(w). -/
theorem available_step {H : Finset (Finset α)} (hlin : Linear H)
    {I : Finset α} {w : α} (hw : w ∈ available H I) :
    ((available H (insert w I)).card:ℝ) =
      (available H I).card-1-(incident H I 2 w).card := by
  have hh := available_card_step hw
  rw [← hlin.incident_two_card I w hw] at hh
  have hhR : ((available H (insert w I)).card:ℝ)+1+(incident H I 2 w).card =
      (available H I).card := by exact_mod_cast hh
  linarith

/-- Two-sided local degree bounds propagate two-sided availability bounds. -/
lemma profile_step {H : Finset (Finset α)} (hlin : Linear H)
    (lower upper : ℕ → ℝ) {n : ℕ} {I : Finset α} {w : α}
    (hw : w ∈ available H I)
    (hq : remaining H upper n ≤ ((available H I).card:ℝ) ∧
      ((available H I).card:ℝ) ≤ remaining H lower n)
    (hd : lower n ≤ ((incident H I 2 w).card:ℝ) ∧
      ((incident H I 2 w).card:ℝ) ≤ upper n) :
    remaining H upper (n+1) ≤ ((available H (insert w I)).card:ℝ) ∧
      ((available H (insert w I)).card:ℝ) ≤ remaining H lower (n+1) := by
  rw [available_step hlin hw,remaining_step,remaining_step]
  constructor <;> linarith only [hq.1,hq.2,hd.1,hd.2]

/-- Whenever the bookkeeping is still running, all previous genuine
    choices passed its guard. Hence guard-implied degree bounds already
    give the availability invariant at every reachable running state. This
    lets a future guard include that invariant without circular reasoning. -/
theorem reach_running_profiles {H : Finset (Finset α)} (hlin : Linear H)
    {L T : ℕ} (hL : 0 < L) {G : ℕ → Tracked H T → Prop}
    (lower upper : ℕ → ℝ)
    (hbudget : ∀ k ≤ T, (L:ℝ) ≤ remaining H upper k)
    (hdegree : ∀ k < T, ∀ z, G k z → z.running = true → Ready H L z.chosen →
      ∀ w ∈ available H z.chosen,
        lower k ≤ ((incident H z.chosen 2 w).card:ℝ) ∧
          ((incident H z.chosen 2 w).card:ℝ) ≤ upper k)
    {n : ℕ} {s : Tracked H T} (hs : GreedyTrackedState.Reach H L T G n s)
    (hrun : s.running = true) :
    remaining H upper n ≤ ((available H s.chosen).card:ℝ) ∧
      ((available H s.chosen).card:ℝ) ≤ remaining H lower n := by
  induction hs with
  | initial => simp [remaining,initial]
  | @action n s a hs hn ha ih =>
    cases a with
    | none =>
      have hq := ih hrun
      have hr : Ready H L s.chosen := by
        apply (ready_iff H L hL s.chosen).mpr
        exact_mod_cast (hbudget n hn.le).trans hq.1
      exact ((mem_actions_none H L s.chosen).mp ha hr).elim
    | some w =>
      have hg : s.running = true ∧ G n s := by
        by_contra h
        have hh := (update_guard_failed w h).2.2
        rw [hrun] at hh
        contradiction
      have hq := ih hg.1
      obtain ⟨hr,hw⟩ := (mem_actions_some H L s.chosen w).mp ha
      have hd := hdegree n hn s hg.2 hg.1 hr w hw
      simpa only [update_chosen,GreedyFiniteKernel.move] using profile_step hlin lower upper hw hq hd

/-- Pathwise integration of local two-degree profiles. The explicit lower
    budget ensures that every transition is a genuine choice, not a hold. -/
theorem goodPath_profile_terminal {H : Finset (Finset α)} (hlin : Linear H)
    {L T : ℕ} (hL : 0 < L) {G : ℕ → Tracked H T → Prop}
    (P : ℕ → Tracked H T → Prop) (lower upper : ℕ → ℝ)
    (hbudget : ∀ k ≤ T, (L:ℝ) ≤ remaining H upper k)
    (hguard : ∀ k < T, ∀ z, GreedyTrackedState.Reach H L T G k z →
      z.running = true → ¬P k z → G k z)
    (hdegree : ∀ k < T, ∀ z, GreedyTrackedState.Reach H L T G k z →
      z.running = true → Ready H L z.chosen → ¬P k z →
      ∀ w ∈ available H z.chosen,
        lower k ≤ ((incident H z.chosen 2 w).card:ℝ) ∧
          ((incident H z.chosen 2 w).card:ℝ) ≤ upper k)
    {n h : ℕ} {s : Tracked H T}
    (hs : GreedyTrackedState.Reach H L T G n s) (hrun : s.running = true)
    (hnh : n+h ≤ T)
    (hq : remaining H upper n ≤ ((available H s.chosen).card:ℝ) ∧
      ((available H s.chosen).card:ℝ) ≤ remaining H lower n)
    (hp : GoodPath (GreedyTrackedState.kernel H L T G) P n h s) :
    ∃ z, GreedyTrackedState.Reach H L T G (n+h) z ∧ z.running = true ∧
      (remaining H upper (n+h) ≤ ((available H z.chosen).card:ℝ) ∧
        ((available H z.chosen).card:ℝ) ≤ remaining H lower (n+h)) ∧ ¬P (n+h) z := by
  induction h generalizing n s with
  | zero => exact ⟨s,hs,hrun,hq,hp⟩
  | succ h ih =>
    obtain ⟨hnp,z,hz,hp⟩ := hp
    have hg := hguard n (by omega) s hs hrun hnp
    have hr : Ready H L s.chosen := by
      apply (ready_iff H L hL s.chosen).mpr
      exact_mod_cast (hbudget n (by omega)).trans hq.1
    have hzr : GreedyTrackedState.Reach H L T G (n+1) z := hs.kernel_step (by omega) hz
    have hstep : z.running = true ∧
        remaining H upper (n+1) ≤ ((available H z.chosen).card:ℝ) ∧
          ((available H z.chosen).card:ℝ) ≤ remaining H lower (n+1) := by
      obtain ⟨a,ha,rfl⟩ := (GreedyTrackedState.kernel_support H L T G n s z).mp hz
      cases a with
      | none => exact ((mem_actions_none H L s.chosen).mp ha hr).elim
      | some w =>
        have hw := ((mem_actions_some H L s.chosen w).mp ha).2
        have hd := hdegree n (by omega) s hs hrun hr hnp w hw
        refine ⟨by simp [update,hrun,hg],?_⟩
        simpa only [update_chosen,GreedyFiniteKernel.move] using profile_step hlin lower upper hw hq hd
    have hh := ih (n := n+1) hzr hstep.1 (by omega) hstep.2 hp
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- A profile-controlled avoiding path yields a full independent run once
    the sum of proposed losses leaves at least L available vertices. -/
theorem full_run_of_profiles {H : Finset (Finset α)} (hlin : Linear H)
    (hH : ∀ e ∈ H, e.Nonempty) {L T : ℕ} (hL : 0 < L)
    {G : ℕ → Tracked H T → Prop} (P : ℕ → Tracked H T → Prop)
    (lower upper : ℕ → ℝ)
    (hupper : ∀ k < T, 0 ≤ 1+upper k)
    (hbudget : (L:ℝ) ≤ remaining H upper T)
    (hguard : ∀ k < T, ∀ z, GreedyTrackedState.Reach H L T G k z →
      z.running = true → ¬P k z → G k z)
    (hdegree : ∀ k < T, ∀ z, GreedyTrackedState.Reach H L T G k z →
      z.running = true → Ready H L z.chosen → ¬P k z →
      ∀ w ∈ available H z.chosen,
        lower k ≤ ((incident H z.chosen 2 w).card:ℝ) ∧
          ((incident H z.chosen 2 w).card:ℝ) ≤ upper k)
    (hp : GoodPath (GreedyTrackedState.kernel H L T G) P 0 T (initial H T)) :
    ∃ z, GreedyTrackedState.Reach H L T G T z ∧ z.running = true ∧ Valid H L T z ∧
      Independent H z.chosen ∧ z.chosen.card = T ∧
      (remaining H upper T ≤ ((available H z.chosen).card:ℝ) ∧
        ((available H z.chosen).card:ℝ) ≤ remaining H lower T) ∧ ¬P T z := by
  have hzero : remaining H upper 0 ≤ ((available H (initial H T).chosen).card:ℝ) ∧
      ((available H (initial H T).chosen).card:ℝ) ≤ remaining H lower 0 := by
    simp [remaining,initial]
  obtain ⟨z,hz,hrun,hq,hp⟩ := goodPath_profile_terminal hlin hL P lower upper
    (remaining_budget hupper hbudget) hguard hdegree GreedyTrackedState.Reach.initial rfl (by omega) hzero hp
  simp only [Nat.zero_add] at hz hq hp
  have hr : Ready H L z.chosen := by
    apply (ready_iff H L hL z.chosen).mpr
    exact_mod_cast hbudget.trans hq.1
  have hcard : z.chosen.card = T := by
    rcases hz.carrier.card_or_stopped hL with h | h
    · exact h
    · exact (Nat.not_lt_of_ge hr.1 h).elim
  exact ⟨z,hz,hrun,hz.valid,hz.carrier.independent hH,hcard,hq,hp⟩

#print axioms remaining_discrete
#print axioms remaining_discrete_lower
#print axioms reach_running_profiles
#print axioms remaining_budget
#print axioms available_step
#print axioms profile_step
#print axioms goodPath_profile_terminal
#print axioms full_run_of_profiles
end
end Erdos773.GreedyAvailableProfiles
