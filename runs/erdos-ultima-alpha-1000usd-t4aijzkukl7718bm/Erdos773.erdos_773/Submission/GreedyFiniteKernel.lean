import Submission.FiniteKernelChoices
import Submission.StoppedGreedyMoments
import Submission.GreedyConfigurationTails

/-!
The stopped greedy average as a genuine finite kernel. A lifting interface
permits finite auxiliary memory without silently altering the selected-set
process. No tracked-memory implementation or long-running-time bound is
asserted in this file.
-/
namespace Erdos773.GreedyFiniteKernel
open Finset GreedyHypergraphState StoppedGreedyMoments FiniteKernelCrossing FiniteKernelChoices
set_option maxHeartbeats 2000000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def actions (H : Finset (Finset α)) (L : ℕ) (I : Finset α) : Finset (Option α) := by
  classical
  exact if Ready H L I then (available H I).image some else {none}

lemma actions_nonempty (H : Finset (Finset α)) (L : ℕ) (I : Finset α) : (actions H L I).Nonempty := by
  classical
  unfold actions
  split_ifs with h
  · exact h.2.image some
  · exact singleton_nonempty _

def move (I : Finset α) (a : Option α) : Finset α :=
  match a with
  | none => I
  | some v => insert v I

def kernel (H : Finset (Finset α)) (L : ℕ) : Kernel (Finset α) :=
  ofChoices (actions H L) (actions_nonempty H L) move

/-- The kernel averages agree exactly with the previously proved stopped
    expectation's one-step operator. -/
theorem kernel_avg (H : Finset (Finset α)) (L : ℕ) (f : Finset α → ℝ) (I : Finset α) :
    (kernel H L).avg f I = step H L f I := by
  classical
  rw [kernel,ofChoices_avg]
  unfold step actions
  split_ifs with h
  · rw [card_image_of_injective _ (Option.some_injective α)]
    rw [sum_image (fun a _ b _ hab => Option.some.inj hab)]
    rfl
  · simp [move]

theorem kernel_support (H : Finset (Finset α)) (L : ℕ) (I J : Finset α) :
    0 < (kernel H L).weight I J ↔
      (Ready H L I ∧ ∃ v ∈ available H I, J = insert v I) ∨ (¬Ready H L I ∧ J = I) := by
  classical
  rw [kernel,ofChoices_support]
  by_cases h : Ready H L I <;> simp [actions,move,h,eq_comm]

lemma kernel_subset {H : Finset (Finset α)} {L : ℕ} {I J : Finset α}
    (hJ : 0 < (kernel H L).weight I J) : I ⊆ J := by
  rcases (kernel_support H L I J).mp hJ with ⟨_,v,_,rfl⟩ | ⟨_,rfl⟩
  · exact subset_insert v I
  · exact Subset.refl _

lemma reach_step {H : Finset (Finset α)} {L n : ℕ} {I J : Finset α}
    (hI : Reach H L n I) (hJ : 0 < (kernel H L).weight I J) : Reach H L (n+1) J := by
  rcases (kernel_support H L I J).mp hJ with ⟨hr,v,hv,rfl⟩ | ⟨hr,rfl⟩
  · exact hI.choose hr hv
  · exact hI.hold hr

/-- A good kernel path ends at an actual reachable greedy state. -/
theorem goodPath_terminal {H : Finset (Finset α)} {L n h : ℕ} {I : Finset α}
    (P : ℕ → Finset α → Prop) (hI : Reach H L n I)
    (hp : GoodPath (fun _ => kernel H L) P n h I) :
    ∃ J, Reach H L (n+h) J ∧ ¬P (n+h) J := by
  induction h generalizing n I with
  | zero => exact ⟨I,by simpa using hI,by simpa using hp⟩
  | succ h ih =>
    obtain ⟨_,J,hJ,hp⟩ := hp
    obtain ⟨S,hS,hgood⟩ := ih (reach_step hI hJ) hp
    exact ⟨S,by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hS,
      by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hgood⟩

/-- The early-stopping alternative is retained after concentration-path
    extraction. A separate theorem must exclude it. -/
theorem goodPath_independent {H : Finset (Finset α)} (hH : ∀ e ∈ H, e.Nonempty)
    (L : ℕ) (hL : 0 < L) (t : ℕ) (P : ℕ → Finset α → Prop)
    (hp : GoodPath (fun _ => kernel H L) P 0 t ∅) :
    ∃ I, Reach H L t I ∧ Independent H I ∧
      (I.card = t ∨ (available H I).card < L) ∧ ¬P t I := by
  obtain ⟨I,hI,hP⟩ := goodPath_terminal P Reach.zero hp
  simp only [Nat.zero_add] at hI hP
  exact ⟨I,hI,hI.independent hH,hI.card_or_stopped hL,hP⟩

def iterateStep (H : Finset (Finset α)) (L : ℕ) : ℕ → (Finset α → ℝ) → Finset α → ℝ
  | 0, f => f
  | h+1, f => step H L (iterateStep H L h f)

lemma iterateStep_step (H : Finset (Finset α)) (L h : ℕ) (f : Finset α → ℝ) :
    iterateStep H L h (step H L f) = step H L (iterateStep H L h f) := by
  induction h with
  | zero => rfl
  | succ h ih => simp only [iterateStep,ih]

lemma expectation_eq_iterateStep (H : Finset (Finset α)) (L h : ℕ) (f : Finset α → ℝ) :
    expectation H L h f = iterateStep H L h f ∅ := by
  induction h generalizing f with
  | zero => rfl
  | succ h ih => rw [expectation,ih,iterateStep_step]; rfl

section Lift
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Push the same greedy actions through an auxiliary-state update. -/
def liftedKernel (H : Finset (Finset α)) (L : ℕ) (carrier : σ → Finset α)
    (next : σ → Option α → σ) : Kernel σ :=
  ofChoices (fun s => actions H L (carrier s)) (fun s => actions_nonempty H L (carrier s)) next

/-- Auxiliary memory may change, but the projected one-step expectation is
    exactly the stopped greedy one when supported updates have the right carrier. -/
theorem lifted_avg (H : Finset (Finset α)) (L : ℕ) (carrier : σ → Finset α)
    (next : σ → Option α → σ)
    (hnext : ∀ s a, a ∈ actions H L (carrier s) → carrier (next s a) = move (carrier s) a)
    (f : Finset α → ℝ) (s : σ) :
    (liftedKernel H L carrier next).avg (fun z => f (carrier z)) s = step H L f (carrier s) := by
  rw [← kernel_avg H L f (carrier s),liftedKernel,kernel,ofChoices_avg,ofChoices_avg]
  congr 1
  apply sum_congr rfl
  intro a ha
  rw [hnext s a ha]

theorem lifted_support (H : Finset (Finset α)) (L : ℕ) (carrier : σ → Finset α)
    (next : σ → Option α → σ)
    (hnext : ∀ s a, a ∈ actions H L (carrier s) → carrier (next s a) = move (carrier s) a)
    {s z : σ} (hz : 0 < (liftedKernel H L carrier next).weight s z) :
    0 < (kernel H L).weight (carrier s) (carrier z) := by
  obtain ⟨a,ha,rfl⟩ := (ofChoices_support _ _ _ s z).mp hz
  apply (ofChoices_support _ _ _ _ _).mpr
  exact ⟨a,ha,(hnext s a ha).symm⟩

/-- Arbitrary finite auxiliary memory does not change any terminal moment
    of the selected carrier, if its supported updates have the right carrier. -/
theorem lifted_terminal (H : Finset (Finset α)) (L : ℕ)
    (carrier : σ → Finset α) (next : ℕ → σ → Option α → σ)
    (hnext : ∀ n s a, a ∈ actions H L (carrier s) → carrier (next n s a) = move (carrier s) a)
    (n h : ℕ) (f : Finset α → ℝ) (s : σ) :
    terminal (fun n => liftedKernel H L carrier (next n)) n h (fun z => f (carrier z)) s =
      iterateStep H L h f (carrier s) := by
  induction h generalizing n s with
  | zero => rfl
  | succ h ih =>
    rw [terminal]
    have heq : terminal (fun n => liftedKernel H L carrier (next n)) (n+1) h
        (fun z => f (carrier z)) = fun z => iterateStep H L h f (carrier z) :=
      funext (fun z => ih (n+1) z)
    rw [heq,lifted_avg H L carrier (next n) (hnext n)]
    rfl

theorem lifted_terminal_from_empty (H : Finset (Finset α)) (L : ℕ)
    (carrier : σ → Finset α) (next : ℕ → σ → Option α → σ)
    (hnext : ∀ n s a, a ∈ actions H L (carrier s) → carrier (next n s a) = move (carrier s) a)
    (h : ℕ) (f : Finset α → ℝ) (s : σ) (hs : carrier s = ∅) :
    terminal (fun n => liftedKernel H L carrier (next n)) 0 h (fun z => f (carrier z)) s =
      expectation H L h f := by
  rw [lifted_terminal H L carrier next hnext,hs,expectation_eq_iterateStep]

/-- Monotone selected-set bad events have exactly the same first-crossing
    probability under any admissible finite-memory lift as their old terminal
    expectation. Thus the already proved all-subset witness tails transfer. -/
theorem lifted_hit_of_monotone (H : Finset (Finset α)) (L : ℕ)
    (carrier : σ → Finset α) (next : ℕ → σ → Option α → σ)
    (hnext : ∀ n s a, a ∈ actions H L (carrier s) → carrier (next n s a) = move (carrier s) a)
    (P : Finset α → Prop) (hP : ∀ I J, I ⊆ J → P I → P J)
    (t : ℕ) (s : σ) (hs : carrier s = ∅) :
    hit (fun n => liftedKernel H L carrier (next n)) (fun _ z => P (carrier z)) 0 t s =
      expectation H L t (GreedyConfigurationTails.event P) := by
  have hf : ∀ n < t, ∀ x y,
      0 < (liftedKernel H L carrier (next n)).weight x y → P (carrier x) → P (carrier y) := by
    intro n hn x y hxy hx
    exact hP _ _ (kernel_subset (lifted_support H L carrier (next n) (hnext n) hxy)) hx
  calc
    _ = terminal (fun n => liftedKernel H L carrier (next n)) 0 t
        (hit (fun n => liftedKernel H L carrier (next n)) (fun _ z => P (carrier z)) (0+t) 0) s :=
      (terminal_eq_hit_of_preserved _ _ t hf 0 t (by omega) s).symm
    _ = _ := by
      change terminal (fun n => liftedKernel H L carrier (next n)) 0 t
        (fun z => GreedyConfigurationTails.event P (carrier z)) s = _
      exact lifted_terminal_from_empty H L carrier next hnext t _ s hs

/-- A finite-memory path projects to genuine reachable greedy states. The
    next-state map may depend on time; its memory invariants remain the
    responsibility of the application. -/
theorem lifted_goodPath_terminal (H : Finset (Finset α)) (L : ℕ)
    (carrier : σ → Finset α) (next : ℕ → σ → Option α → σ)
    (hnext : ∀ n s a, a ∈ actions H L (carrier s) → carrier (next n s a) = move (carrier s) a)
    (P : ℕ → σ → Prop) (n h : ℕ) (s : σ) (hI : Reach H L n (carrier s))
    (hp : GoodPath (fun n => liftedKernel H L carrier (next n)) P n h s) :
    ∃ z, Reach H L (n+h) (carrier z) ∧ ¬P (n+h) z := by
  induction h generalizing n s with
  | zero => exact ⟨s,by simpa using hI,by simpa using hp⟩
  | succ h ih =>
    obtain ⟨_,z,hz,hp⟩ := hp
    have hreach := reach_step hI (lifted_support H L carrier (next n) (hnext n) hz)
    obtain ⟨z',hr,hgood⟩ := ih (n+1) z hreach hp
    exact ⟨z',by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hr,
      by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hgood⟩

end Lift
#print axioms lifted_hit_of_monotone
#print axioms lifted_terminal
#print axioms lifted_terminal_from_empty
#print axioms kernel_avg
#print axioms kernel_support
#print axioms goodPath_independent
#print axioms lifted_avg
#print axioms lifted_support
#print axioms lifted_goodPath_terminal
end
end Erdos773.GreedyFiniteKernel
