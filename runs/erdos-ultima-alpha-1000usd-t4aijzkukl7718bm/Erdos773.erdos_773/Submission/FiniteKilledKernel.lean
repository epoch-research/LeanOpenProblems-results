import Submission.FiniteKernelCrossing

/-!
Killing a finite kernel AFTER its guard fails. A transition from a good state
still visits its actual destination, including a first bad state or an
overshoot. Only the following transition goes to the cemetery. This makes
first-guard-crossing probabilities invariant under killing.
-/
namespace Erdos773.FiniteKilledKernel
open Finset FiniteKernelCrossing
set_option maxHeartbeats 2500000
noncomputable section
variable {σ : Type*} [Fintype σ]

/-- `none` is an absorbing cemetery; a false guard kills the next transition. -/
def kill (K : Kernel σ) (G : σ → Prop) : Kernel (Option σ) where
  weight x y := by
    classical
    exact match x, y with
    | none, none => 1
    | none, some _ => 0
    | some x, none => if G x then 0 else 1
    | some x, some y => if G x then K.weight x y else 0
  nonneg x y := by
    classical
    cases x <;> cases y <;> simp only
    all_goals first | positivity | (split_ifs <;> first | positivity | exact K.nonneg _ _)
  total x := by
    classical
    cases x with
    | none => simp
    | some x => by_cases hG : G x <;> simp [hG, K.total]

/-- Lift an observable, giving it zero value at the cemetery. -/
def liftValue (f : σ → ℝ) : Option σ → ℝ
  | none => 0
  | some x => f x

/-- The cemetery never satisfies a lifted event. -/
def liftEvent (P : σ → Prop) : Option σ → Prop
  | none => False
  | some x => P x

@[simp] theorem avg_none (K : Kernel σ) (G : σ → Prop) (f : Option σ → ℝ) :
    (kill K G).avg f none = f none := by
  classical
  simp [Kernel.avg, kill]

@[simp] theorem avg_some (K : Kernel σ) (G : σ → Prop) [DecidablePred G] (f : Option σ → ℝ) (x : σ) :
    (kill K G).avg f (some x) = if G x then K.avg (fun y => f (some y)) x else f none := by
  classical
  by_cases hG : G x <;> simp [Kernel.avg, kill, hG]

@[simp] theorem support_some (K : Kernel σ) (G : σ → Prop) (x y : σ) :
    0 < (kill K G).weight (some x) (some y) ↔ G x ∧ 0 < K.weight x y := by
  classical
  by_cases hG : G x <;> simp [kill, hG]

@[simp] theorem support_death (K : Kernel σ) (G : σ → Prop) (x : σ) :
    0 < (kill K G).weight (some x) none ↔ ¬G x := by
  classical
  by_cases hG : G x <;> simp [kill, hG]

@[simp] theorem hit_none (K : ℕ → Kernel σ) (G P : ℕ → σ → Prop) (n h : ℕ) :
    hit (fun n => kill (K n) (G n)) (fun n => liftEvent (P n)) n h none = 0 := by
  classical
  induction h generalizing n with
  | zero => simp [hit, liftEvent]
  | succ h ih => simp only [hit, liftEvent, if_false, avg_none, ih]

/-- Killing never increases a lifted event's first-hitting probability. -/
theorem hit_le_original (K : ℕ → Kernel σ) (G P : ℕ → σ → Prop) (n h : ℕ) (x : σ) :
    hit (fun n => kill (K n) (G n)) (fun n => liftEvent (P n)) n h (some x) ≤
      hit K P n h x := by
  classical
  induction h generalizing n x with
  | zero => simp [hit, liftEvent]
  | succ h ih =>
    by_cases hp : P n x
    · simp only [hit, liftEvent, if_pos hp, le_refl]
    · simp only [hit, liftEvent, if_neg hp, avg_some]
      by_cases hG : G n x
      · rw [if_pos hG]
        exact (K n).avg_mono (fun y => ih (n+1) y) x
      · rw [if_neg hG, hit_none]
        exact (K n).avg_nonneg (fun y => (hit_bounds K P (n+1) h y).1) x

/-- Any event including guard failure has exactly its original first-crossing
probability. In particular the first failed guard is not discarded. -/
theorem hit_eq_original (K : ℕ → Kernel σ) (G P : ℕ → σ → Prop) (T : ℕ)
    (hstop : ∀ n ≤ T, ∀ x, ¬G n x → P n x)
    (n h : ℕ) (hnh : n+h ≤ T) (x : σ) :
    hit (fun n => kill (K n) (G n)) (fun n => liftEvent (P n)) n h (some x) =
      hit K P n h x := by
  classical
  induction h generalizing n x with
  | zero => simp [hit, liftEvent]
  | succ h ih =>
    by_cases hp : P n x
    · simp only [hit, liftEvent, if_pos hp]
    · have hG : G n x := by by_contra hn; exact hp (hstop n (by omega) x hn)
      simp only [hit, liftEvent, if_neg hp, avg_some, if_pos hG]
      exact congrArg (fun f => (K n).avg f x)
        (funext (fun y => ih (n+1) (by omega) y))

/-- A guard-local nonnegative potential is globally valid for the killed
kernel. No drift hypothesis is imposed on failed guards or on the cemetery. -/
theorem hit_le_guarded_potential (K : ℕ → Kernel σ) (G P : ℕ → σ → Prop)
    (F : ℕ → σ → ℝ) (T : ℕ) (A : ℝ) (hA : 0 < A)
    (hF : ∀ n ≤ T, ∀ x, 0 ≤ F n x)
    (hstep : ∀ n < T, ∀ x, G n x → (K n).avg (F (n+1)) x ≤ F n x)
    (hdom : ∀ n ≤ T, ∀ x, P n x → A ≤ F n x)
    (n h : ℕ) (hnh : n+h ≤ T) (x : σ) :
    hit (fun n => kill (K n) (G n)) (fun n => liftEvent (P n)) n h (some x) ≤ F n x/A := by
  classical
  apply hit_le_potential _ _ (fun n => liftValue (F n)) T A hA _ _ _ n h hnh (some x)
  · intro n hn x
    cases x with
    | none => exact le_rfl
    | some x => exact hF n hn x
  · intro n hn x
    cases x with
    | none => simp only [avg_none, liftValue, le_refl]
    | some x =>
      rw [avg_some]
      by_cases hG : G n x
      · exact (if_pos hG).trans_le (hstep n hn x hG)
      · rw [if_neg hG]
        exact hF n (by omega) x
  · intro n hn x hp
    cases x with
    | none => exact hp.elim
    | some x => exact hdom n hn x hp

#print axioms kill
#print axioms support_some
#print axioms hit_le_original
#print axioms hit_eq_original
#print axioms hit_le_guarded_potential
end
end Erdos773.FiniteKilledKernel
