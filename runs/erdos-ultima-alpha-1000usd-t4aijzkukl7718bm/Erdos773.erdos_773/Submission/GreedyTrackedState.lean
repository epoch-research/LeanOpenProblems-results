import Submission.GreedyFiniteKernel
import Submission.GreedyLinearHigherDrift

/-!
A concrete finite state recording degrees and last-update clocks. Death of a
vertex freezes its records. A separate guard can freeze ALL records while
the selected-set carrier continues the original stopped greedy process.
-/
namespace Erdos773.GreedyTrackedState
open Finset GreedyHypergraphState StoppedGreedyMoments GreedyFiniteKernel
open FiniteKernelCrossing FiniteKernelChoices
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

structure State (α : Type*) [Fintype α] [DecidableEq α] (M T : ℕ) where
  chosen : Finset α
  counts : Fin 3 → α → Fin (M+1)
  clock : α → Fin (T+1)
  running : Bool
  deriving Fintype

instance (M T : ℕ) : DecidableEq (State α M T) := Classical.decEq _

abbrev Tracked (H : Finset (Finset α)) (T : ℕ) := State α H.card T

def boundedDegree (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (u : α) : Fin (H.card+1) :=
  ⟨(incident H I j u).card,Nat.lt_succ_of_le (card_le_card (incident_subset H I j u))⟩

def clockAt (T n : ℕ) : Fin (T+1) := ⟨min n T,Nat.lt_succ_of_le (min_le_right n T)⟩

def initial (H : Finset (Finset α)) (T : ℕ) : Tracked H T where
  chosen := ∅
  counts j u := boundedDegree H ∅ (j.val+2) u
  clock _ := 0
  running := true

/-- A failed guard stops only the bookkeeping, never silently adds a carrier
    hold. `none` is the existing greedy hold and leaves the entire state fixed. -/
def update (H : Finset (Finset α)) (T : ℕ) (G : ℕ → Tracked H T → Prop)
    (n : ℕ) (s : Tracked H T) (a : Option α) : Tracked H T := by
  classical
  exact match a with
  | none => s
  | some w =>
    if s.running = true ∧ G n s then
      { chosen := insert w s.chosen
        counts := fun j u => if u ∈ available H (insert w s.chosen)
          then boundedDegree H (insert w s.chosen) (j.val+2) u else s.counts j u
        clock := fun u => if u ∈ available H (insert w s.chosen) then clockAt T (n+1) else s.clock u
        running := true }
    else
      { chosen := insert w s.chosen
        counts := s.counts
        clock := s.clock
        running := false }

@[simp] lemma update_chosen (H : Finset (Finset α)) (T : ℕ)
    (G : ℕ → Tracked H T → Prop) (n : ℕ) (s : Tracked H T) (a : Option α) :
    (update H T G n s a).chosen = move s.chosen a := by
  classical
  cases a with
  | none => rfl
  | some w => unfold update; split_ifs <;> rfl

@[simp] lemma update_none (H : Finset (Finset α)) (T : ℕ)
    (G : ℕ → Tracked H T → Prop) (n : ℕ) (s : Tracked H T) : update H T G n s none = s := rfl

lemma update_freezes {H : Finset (Finset α)} {T n : ℕ}
    {G : ℕ → Tracked H T → Prop} {s : Tracked H T} {w u : α}
    (hu : u ∉ available H (insert w s.chosen)) :
    (∀ j, (update H T G n s (some w)).counts j u = s.counts j u) ∧
      (update H T G n s (some w)).clock u = s.clock u := by
  classical
  simp only [update]
  split_ifs <;> simp [hu]

lemma update_guard_failed {H : Finset (Finset α)} {T n : ℕ}
    {G : ℕ → Tracked H T → Prop} {s : Tracked H T} (w : α)
    (hg : ¬(s.running = true ∧ G n s)) :
    (update H T G n s (some w)).counts = s.counts ∧
      (update H T G n s (some w)).clock = s.clock ∧
        (update H T G n s (some w)).running = false := by
  classical
  simp [update,hg]

lemma update_inactive {H : Finset (Finset α)} {T n : ℕ}
    {G : ℕ → Tracked H T → Prop} {s : Tracked H T} (a : Option α)
    (hs : s.running = false) :
    (update H T G n s a).running = false ∧
      (update H T G n s a).counts = s.counts ∧ (update H T G n s a).clock = s.clock := by
  classical
  cases a with
  | none => exact ⟨hs,rfl,rfl⟩
  | some w => simp [update,hs]

/-- Degree coherence is required only while the bookkeeping is running. -/
def Coherent (H : Finset (Finset α)) {T : ℕ} (s : Tracked H T) : Prop :=
  s.running = true → ∀ u ∈ available H s.chosen, ∀ j : Fin 3,
    (s.counts j u).val = (incident H s.chosen (j.val+2) u).card

/-- At an unstopped running state all available clocks equal the step number.
    All clocks, including frozen ones, are bounded by that number. -/
def Valid (H : Finset (Finset α)) (L n : ℕ) {T : ℕ} (s : Tracked H T) : Prop :=
  Coherent H s ∧ (∀ u, (s.clock u).val ≤ n) ∧
    (s.running = true → Ready H L s.chosen → ∀ u ∈ available H s.chosen, (s.clock u).val = n)

lemma initial_valid (H : Finset (Finset α)) (L T : ℕ) : Valid H L 0 (initial H T) := by
  refine ⟨?_,?_,?_⟩
  · intro hs u hu j
    rfl
  · intro u
    exact Nat.zero_le _
  · intro hs hr u hu
    rfl

lemma mem_actions_none (H : Finset (Finset α)) (L : ℕ) (I : Finset α) :
    none ∈ actions H L I ↔ ¬Ready H L I := by
  classical
  by_cases hr : Ready H L I <;> simp [actions,hr]

lemma mem_actions_some (H : Finset (Finset α)) (L : ℕ) (I : Finset α) (w : α) :
    some w ∈ actions H L I ↔ Ready H L I ∧ w ∈ available H I := by
  classical
  by_cases hr : Ready H L I <;> simp [actions,hr]

/-- Coherence and clock bounds hold after every supported update through the
    horizon. Once the guard fails, the coherence condition becomes inactive,
    while the frozen clock bounds continue to hold. -/
theorem update_valid {H : Finset (Finset α)} {L T n : ℕ}
    (G : ℕ → Tracked H T → Prop) (hn : n < T) {s : Tracked H T}
    (hs : Valid H L n s) {a : Option α} (ha : a ∈ actions H L s.chosen) :
    Valid H L (n+1) (update H T G n s a) := by
  classical
  cases a with
  | none =>
    have hr := (mem_actions_none H L s.chosen).mp ha
    refine ⟨hs.1,fun u => (hs.2.1 u).trans (Nat.le_succ n),?_⟩
    intro hrun hready
    exact (hr hready).elim
  | some w =>
    by_cases hg : s.running = true ∧ G n s
    · simp only [update,if_pos hg]
      refine ⟨?_,?_,?_⟩
      · intro hrun u hu j
        simp only [if_pos hu,boundedDegree]
      · intro u
        by_cases hu : u ∈ available H (insert w s.chosen)
        · simp only [if_pos hu,clockAt]
          exact min_le_left _ _
        · simp only [if_neg hu]
          exact (hs.2.1 u).trans (Nat.le_succ n)
      · intro hrun hready u hu
        simp only [if_pos hu,clockAt]
        exact min_eq_left (by omega)
    · simp only [update,if_neg hg]
      refine ⟨?_,fun u => (hs.2.1 u).trans (Nat.le_succ n),?_⟩
      · intro hrun
        contradiction
      · intro hrun
        contradiction

def kernel (H : Finset (Finset α)) (L T : ℕ) (G : ℕ → Tracked H T → Prop) (n : ℕ) : Kernel (Tracked H T) :=
  liftedKernel H L State.chosen (update H T G n)

lemma kernel_support (H : Finset (Finset α)) (L T : ℕ) (G : ℕ → Tracked H T → Prop)
    (n : ℕ) (s z : Tracked H T) :
    0 < (kernel H L T G n).weight s z ↔
      ∃ a ∈ actions H L s.chosen, update H T G n s a = z :=
  ofChoices_support (fun s : Tracked H T => actions H L s.chosen)
    (fun s => actions_nonempty H L s.chosen) (update H T G n) s z

/-- Reachability for the complete recorded state, with the real horizon. -/
inductive Reach (H : Finset (Finset α)) (L T : ℕ) (G : ℕ → Tracked H T → Prop) : ℕ → Tracked H T → Prop
  | initial : Reach H L T G 0 (initial H T)
  | action {n : ℕ} {s : Tracked H T} {a : Option α}
      (hs : Reach H L T G n s) (hn : n < T) (ha : a ∈ actions H L s.chosen) :
      Reach H L T G (n+1) (update H T G n s a)

lemma Reach.valid {H : Finset (Finset α)} {L T n : ℕ} {G : ℕ → Tracked H T → Prop}
    {s : Tracked H T} (hs : Reach H L T G n s) : Valid H L n s := by
  induction hs with
  | initial => exact initial_valid H L T
  | action hs hn ha ih => exact update_valid G hn ih ha

lemma Reach.carrier {H : Finset (Finset α)} {L T n : ℕ} {G : ℕ → Tracked H T → Prop}
    {s : Tracked H T} (hs : Reach H L T G n s) : StoppedGreedyMoments.Reach H L n s.chosen := by
  induction hs with
  | initial => exact StoppedGreedyMoments.Reach.zero
  | @action n s a hs hn ha ih =>
    rw [update_chosen]
    cases a with
    | none => exact ih.hold ((mem_actions_none H L s.chosen).mp ha)
    | some w =>
      obtain ⟨hr,hw⟩ := (mem_actions_some H L s.chosen w).mp ha
      exact ih.choose hr hw

lemma Reach.kernel_step {H : Finset (Finset α)} {L T n : ℕ} {G : ℕ → Tracked H T → Prop}
    {s z : Tracked H T} (hs : Reach H L T G n s) (hn : n < T)
    (hz : 0 < (kernel H L T G n).weight s z) : Reach H L T G (n+1) z := by
  obtain ⟨a,ha,rfl⟩ := (kernel_support H L T G n s z).mp hz
  exact hs.action hn ha

/-- A good path of the recorded kernel terminates at an actually reachable
    recorded state, not merely at a reachable carrier. -/
theorem goodPath_terminal {H : Finset (Finset α)} {L T n h : ℕ}
    {G : ℕ → Tracked H T → Prop} {s : Tracked H T}
    (P : ℕ → Tracked H T → Prop) (hs : Reach H L T G n s) (hnh : n+h ≤ T)
    (hp : GoodPath (kernel H L T G) P n h s) :
    ∃ z, Reach H L T G (n+h) z ∧ ¬P (n+h) z := by
  induction h generalizing n s with
  | zero => exact ⟨s,hs,hp⟩
  | succ h ih =>
    obtain ⟨_,z,hz,hp⟩ := hp
    have hh := ih (n := n+1) (hs.kernel_step (by omega) hz) (by omega) hp
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- In particular, terminal states extracted from a good path have coherent
    live degrees and valid last-update clocks. -/
theorem goodPath_valid_terminal (H : Finset (Finset α)) (L T : ℕ)
    (G : ℕ → Tracked H T → Prop) (P : ℕ → Tracked H T → Prop)
    (hp : GoodPath (kernel H L T G) P 0 T (initial H T)) :
    ∃ z, Reach H L T G T z ∧ Valid H L T z ∧ ¬P T z := by
  obtain ⟨z,hz,hp⟩ := goodPath_terminal P Reach.initial (by omega : 0+T ≤ T) hp
  refine ⟨z,?_,?_,?_⟩
  · simpa only [Nat.zero_add] using hz
  · simpa only [Nat.zero_add] using hz.valid
  · simpa only [Nat.zero_add] using hp

/-- Good states can keep the bookkeeping alive when they imply its guard.
    This is a pathwise implication, with no probabilistic assumption. -/
theorem goodPath_running_terminal {H : Finset (Finset α)} {L T n h : ℕ}
    {G : ℕ → Tracked H T → Prop} {s : Tracked H T}
    (P : ℕ → Tracked H T → Prop)
    (hguard : ∀ k < T, ∀ z, Reach H L T G k z → z.running = true → ¬P k z → G k z)
    (hs : Reach H L T G n s) (hrun : s.running = true) (hnh : n+h ≤ T)
    (hp : GoodPath (kernel H L T G) P n h s) :
    ∃ z, Reach H L T G (n+h) z ∧ z.running = true ∧ ¬P (n+h) z := by
  induction h generalizing n s with
  | zero => exact ⟨s,hs,hrun,hp⟩
  | succ h ih =>
    obtain ⟨hnp,z,hz,hp⟩ := hp
    have hg := hguard n (by omega) s hs hrun hnp
    have hzrun : z.running = true := by
      obtain ⟨a,ha,rfl⟩ := (kernel_support H L T G n s z).mp hz
      cases a with
      | none => exact hrun
      | some w => simp [update,hrun,hg]
    have hh := ih (n := n+1) (hs.kernel_step (by omega) hz) hzrun (by omega) hp
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- If good reachable states imply both the bookkeeping guard and readiness,
    an avoiding path certifies a full T-step independent carrier. The
    readiness implication is a separate, indispensable hypothesis. -/
theorem goodPath_full_run (H : Finset (Finset α)) (hH : ∀ e ∈ H, e.Nonempty)
    (L T : ℕ) (hL : 0 < L) (G : ℕ → Tracked H T → Prop)
    (P : ℕ → Tracked H T → Prop)
    (hguard : ∀ k < T, ∀ z, Reach H L T G k z → z.running = true → ¬P k z → G k z)
    (hready : ∀ z, Reach H L T G T z → z.running = true → ¬P T z → Ready H L z.chosen)
    (hp : GoodPath (kernel H L T G) P 0 T (initial H T)) :
    ∃ z, Reach H L T G T z ∧ z.running = true ∧ Valid H L T z ∧
      Independent H z.chosen ∧ z.chosen.card = T ∧ ¬P T z := by
  obtain ⟨z,hz,hrun,hp⟩ := goodPath_running_terminal P hguard Reach.initial rfl (by omega) hp
  simp only [Nat.zero_add] at hz hp
  have hr := hready z hz hrun hp
  have hc := hz.carrier.card_or_stopped hL
  have hcard : z.chosen.card = T := by rcases hc with h | h; exact h; exact (Nat.not_lt_of_ge hr.1 h).elim
  exact ⟨z,hz,hrun,hz.valid,hz.carrier.independent hH,hcard,hp⟩

/-- The guard and all frozen records leave the carrier's law unchanged. -/
theorem terminal_carrier (H : Finset (Finset α)) (L T : ℕ) (G : ℕ → Tracked H T → Prop)
    (t : ℕ) (f : Finset α → ℝ) :
    terminal (kernel H L T G) 0 t (fun s => f s.chosen) (initial H T) = expectation H L t f := by
  exact lifted_terminal_from_empty H L State.chosen (update H T G)
    (fun n s a _ => update_chosen H T G n s a) t f (initial H T) rfl

/-- Previously proved monotone-event witness tails apply to this concrete
    process, even after its records freeze. -/
theorem hit_carrier (H : Finset (Finset α)) (L T : ℕ) (G : ℕ → Tracked H T → Prop)
    (P : Finset α → Prop) (hP : ∀ I J, I ⊆ J → P I → P J) (t : ℕ) :
    hit (kernel H L T G) (fun _ s => P s.chosen) 0 t (initial H T) =
      expectation H L t (GreedyConfigurationTails.event P) := by
  exact lifted_hit_of_monotone H L State.chosen (update H T G)
    (fun n s a _ => update_chosen H T G n s a) P hP t (initial H T) rfl

#print axioms goodPath_running_terminal
#print axioms goodPath_full_run
#print axioms goodPath_terminal
#print axioms goodPath_valid_terminal
#print axioms update_freezes
#print axioms update_inactive
#print axioms update_valid
#print axioms Reach.valid
#print axioms Reach.carrier
#print axioms terminal_carrier
#print axioms hit_carrier
end
end Erdos773.GreedyTrackedState
