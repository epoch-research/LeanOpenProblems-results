import Submission.GreedyTrackedVariance
import Submission.FiniteFreedman

/-!
Signed first-crossing bounds for the concrete frozen-degree process.
The hypotheses below are quantitative obligations, not an assertion that
any useful profile or guard already satisfies them.
-/
namespace Erdos773.GreedyRecordedCrossing
open Finset GreedyHypergraphState StoppedGreedyMoments
open FiniteKernelCrossing GreedyTrackedState GreedyTrackedMoments GreedyTrackedVariance
open GreedyLinearLocal
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Explicit deterministic controls on running, guard-satisfying states.
    A sign of 1 controls upper deviations and -1 controls lower deviations. -/
structure MomentControl (H : Finset (Finset α)) (L T : ℕ)
    (G : ℕ → Tracked H T → Prop) (f : ℕ → ℝ) (j : Fin 3) (u : α)
    (sign b : ℝ) (B v : ℕ → ℝ) : Prop where
  sign_abs : |sign| = 1
  valid : ∀ n < T, ∀ s, G n s → Valid H L n s
  bound_nonneg : ∀ n < T, 0 ≤ B n
  variance_nonneg : ∀ n < T, 0 ≤ v n
  cap : ∀ n < T, B n+|f (n+1)-f n| ≤ b
  local_bound : ∀ n < T, ∀ s, Ready H L s.chosen → s.running = true → G n s →
    ∀ w ∈ safeChoices H s.chosen u,
      |((incident H (insert w s.chosen) (j.val+2) u).card:ℝ)-
        (incident H s.chosen (j.val+2) u).card| ≤ B n
  local_variance : ∀ n < T, ∀ s, Ready H L s.chosen → s.running = true → G n s →
    2*((∑ w ∈ safeChoices H s.chosen u,
      (((incident H (insert w s.chosen) (j.val+2) u).card:ℝ)-
        (incident H s.chosen (j.val+2) u).card)^2)/(available H s.chosen).card)+
      2*(f (n+1)-f n)^2 ≤ v n

/-- In addition to the increment and variance controls, impose a signed
    nonpositive conditional drift throughout the active guard. -/
structure Control (H : Finset (Finset α)) (L T : ℕ)
    (G : ℕ → Tracked H T → Prop) (f : ℕ → ℝ) (j : Fin 3) (u : α)
    (sign b : ℝ) (B v : ℕ → ℝ) : Prop extends MomentControl H L T G f j u sign b B v where
  local_drift : ∀ n < T, ∀ s, Ready H L s.chosen → s.running = true → G n s →
    sign*(survivalDrift H s.chosen (j.val+2) u-
      (safeChoices H s.chosen u).card*(f (n+1)-f n)) ≤ 0

variable {H : Finset (Finset α)} {L T : ℕ} {G : ℕ → Tracked H T → Prop}
variable {f : ℕ → ℝ} {j : Fin 3} {u : α} {sign b : ℝ} {B v : ℕ → ℝ}

lemma MomentControl.increment (hc : MomentControl H L T G f j u sign b B v)
    {n : ℕ} (hn : n < T) {s z : Tracked H T}
    (hz : 0 < (GreedyTrackedState.kernel H L T G n).weight s z) :
    |sign*(error f z j u-error f s j u)| ≤ b := by
  rw [abs_mul,hc.sign_abs,one_mul]
  by_cases hr : Ready H L s.chosen
  · by_cases hg : s.running = true ∧ G n s
    · exact (profile_increment_bound (hc.valid n hn s hg.2) hn hr hg f j u (B n)
        (hc.bound_nonneg n hn) (hc.local_bound n hn s hr hg.1 hg.2) hz).trans (hc.cap n hn)
    · obtain ⟨a,ha,rfl⟩ := (GreedyTrackedState.kernel_support H L T G n s z).mp hz
      rw [error_increment_frozen hg,abs_zero]
      exact (add_nonneg (hc.bound_nonneg n hn) (abs_nonneg _)).trans (hc.cap n hn)
  · rw [kernel_eq_of_not_ready hr hz,sub_self,abs_zero]
    exact (add_nonneg (hc.bound_nonneg n hn) (abs_nonneg _)).trans (hc.cap n hn)

lemma Control.drift (hc : Control H L T G f j u sign b B v)
    {n : ℕ} (hn : n < T) (s : Tracked H T) :
    (GreedyTrackedState.kernel H L T G n).avg
      (fun z => sign*(error f z j u-error f s j u)) s ≤ 0 := by
  rw [Kernel.avg_mul]
  by_cases hr : Ready H L s.chosen
  · by_cases hg : s.running = true ∧ G n s
    · rw [error_drift (hc.valid n hn s hg.2) hn hr hg,← mul_div_assoc]
      exact div_nonpos_of_nonpos_of_nonneg (hc.local_drift n hn s hr hg.1 hg.2) (by positivity)
    · rw [error_drift_frozen hg,mul_zero]
  · rw [kernel_avg_not_ready G s hr,sub_self,mul_zero]

lemma MomentControl.second_moment (hc : MomentControl H L T G f j u sign b B v)
    {n : ℕ} (hn : n < T) (s : Tracked H T) :
    (GreedyTrackedState.kernel H L T G n).avg
      (fun z => (sign*(error f z j u-error f s j u))^2) s ≤ v n := by
  have hsign : sign^2 = 1 := by nlinarith only [sq_abs sign,hc.sign_abs]
  simp only [mul_pow,hsign,one_mul]
  by_cases hr : Ready H L s.chosen
  · by_cases hg : s.running = true ∧ G n s
    · have hs := hc.valid n hn s hg.2
      have hh := error_second_moment hs hn hr hg f j u
      rw [degree_second_moment hs.1 hr hg] at hh
      exact hh.trans (hc.local_variance n hn s hr hg.1 hg.2)
    · rw [error_second_moment_frozen hg]
      exact hc.variance_nonneg n hn
  · rw [kernel_avg_not_ready G s hr,sub_self,zero_pow (by decide : 2 ≠ 0)]
    exact hc.variance_nonneg n hn

/-- Actual signed recorded-error first crossings. Frozen clocks ensure that
    the profile itself freezes whenever the associated degree freezes. -/
theorem first_crossing (hc : Control H L T G f j u sign b B v)
    (a : ℝ) (hb : 0 < b) (ha : 0 < a) :
    hit (GreedyTrackedState.kernel H L T G)
      (fun _ s => a ≤ sign*(error f s j u-error f (initial H T) j u))
      0 T (initial H T) ≤
        Real.exp (-(a^2)/(4*((∑ n ∈ range T, v n)+b*a))) := by
  let X : ℕ → Tracked H T → ℝ := fun _ s =>
    sign*(error f s j u-error f (initial H T) j u)
  have hdelta (n : ℕ) (s z : Tracked H T) :
      X (n+1) z-X n s = sign*(error f z j u-error f s j u) := by dsimp [X]; ring
  apply FiniteFreedman.first_crossing_deterministic (GreedyTrackedState.kernel H L T G)
    X v T (initial H T) b a hb ha hc.variance_nonneg
  · simp [X]
  · intro n hn s z hz
    rw [hdelta n]
    exact hc.toMomentControl.increment hn hz
  · intro n hn s
    simp only [hdelta]
    exact hc.drift hn s
  · intro n hn s
    simp only [hdelta]
    exact hc.toMomentControl.second_moment hn s

/-- One controlled deviation has a support-respecting avoiding path. This
    still says nothing about how long the selected-set carrier runs. -/
theorem goodPath (hc : Control H L T G f j u sign b B v)
    (a : ℝ) (hb : 0 < b) (ha : 0 < a) :
    GoodPath (GreedyTrackedState.kernel H L T G)
      (fun _ s => a ≤ sign*(error f s j u-error f (initial H T) j u))
      0 T (initial H T) := by
  apply goodPath_of_hit_lt_one
  apply (first_crossing hc a hb ha).trans_lt
  apply Real.exp_lt_one_iff.mpr
  have hv : 0 ≤ ∑ n ∈ range T, v n :=
    sum_nonneg (fun n hn => hc.variance_nonneg n (mem_range.mp hn))
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos ha)) (by positivity)

/-- The avoiding terminal state has the full recorded-state invariant. Its
    carrier may nevertheless have stopped before selecting T vertices. -/
theorem reachable_good (hc : Control H L T G f j u sign b B v)
    (a : ℝ) (hb : 0 < b) (ha : 0 < a) :
    ∃ s, GreedyTrackedState.Reach H L T G T s ∧ Valid H L T s ∧
      sign*(error f s j u-error f (initial H T) j u) < a := by
  obtain ⟨s,hs,hv,hg⟩ := goodPath_valid_terminal H L T G _ (goodPath hc a hb ha)
  exact ⟨s,hs,hv,lt_of_not_ge hg⟩

#print axioms MomentControl.increment
#print axioms Control.drift
#print axioms MomentControl.second_moment
#print axioms first_crossing
#print axioms goodPath
#print axioms reachable_good
end
end Erdos773.GreedyRecordedCrossing
