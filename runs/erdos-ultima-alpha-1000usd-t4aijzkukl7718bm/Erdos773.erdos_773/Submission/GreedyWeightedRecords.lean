import Submission.GreedyTrackedMoments

/-!
Clock-weighted degree records. A deterministic integrating factor may now
multiply the recorded degree, without making the profile clock advance at
vertex death or after a bookkeeping freeze. No horizon is asserted here.
-/
namespace Erdos773.GreedyWeightedRecords
open Finset GreedyHypergraphState StoppedGreedyMoments GreedyFiniteKernel
open FiniteKernelCrossing GreedyTrackedState GreedyTrackedMoments GreedyLinearLocal
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def weightedError {H : Finset (Finset α)} {T : ℕ} (w f : ℕ → ℝ)
    (s : Tracked H T) (j : Fin 3) (u : α) : ℝ :=
  w (s.clock u).val*degree s j u-f (s.clock u).val

/-- The extra deterministic term on a surviving record. It depends on the
current local degree, not on an unproved deterministic mean profile. -/
def offset {H : Finset (Finset α)} {T : ℕ} (w f : ℕ → ℝ)
    (n : ℕ) (s : Tracked H T) (j : Fin 3) (u : α) : ℝ :=
  (w (n+1)-w n)*(incident H s.chosen (j.val+2) u).card-(f (n+1)-f n)

lemma weightedError_eq_live {H : Finset (Finset α)} {L T n : ℕ} {s : Tracked H T}
    (hs : Valid H L n s) (hrun : s.running = true) (hr : Ready H L s.chosen)
    (w f : ℕ → ℝ) (j : Fin 3) {u : α} (hu : u ∈ available H s.chosen) :
    weightedError w f s j u = w n*(incident H s.chosen (j.val+2) u).card-f n := by
  unfold weightedError degree
  rw [hs.1 hrun u hu j,hs.2.2 hrun hr u hu]

lemma weighted_increment {H : Finset (Finset α)} {L T n : ℕ}
    {G : ℕ → Tracked H T → Prop} {s : Tracked H T} (hs : Valid H L n s) (hn : n < T)
    (hr : Ready H L s.chosen) (hg : s.running = true ∧ G n s)
    (w f : ℕ → ℝ) (j : Fin 3) (u v : α) :
    weightedError w f (update H T G n s (some v)) j u-weightedError w f s j u =
      if u ∈ available H (insert v s.chosen) then
        w (n+1)*(((incident H (insert v s.chosen) (j.val+2) u).card:ℝ)-
          (incident H s.chosen (j.val+2) u).card)+offset w f n s j u else 0 := by
  classical
  by_cases hu : u ∈ available H (insert v s.chosen)
  · have hu0 := available_antitone (subset_insert v s.chosen) hu
    have hclock := hs.2.2 hg.1 hr u hu0
    have hdegree := hs.1 hg.1 u hu0 j
    simp only [weightedError,degree,update,if_pos hg,if_pos hu,boundedDegree,clockAt]
    rw [min_eq_left (by omega : n+1 ≤ T),hclock,hdegree]
    dsimp [offset]
    ring
  · simp [weightedError,degree,update,hg,hu]

lemma weighted_increment_frozen {H : Finset (Finset α)} {T n : ℕ}
    {G : ℕ → Tracked H T → Prop} {s : Tracked H T}
    (hg : ¬(s.running = true ∧ G n s)) (w f : ℕ → ℝ) (j : Fin 3) (u : α) (a : Option α) :
    weightedError w f (update H T G n s a) j u-weightedError w f s j u = 0 := by
  classical
  cases a <;> simp [weightedError,degree,update,hg]

/-- Exact conditional mean, including BOTH safe-count corrections. -/
theorem weighted_drift {H : Finset (Finset α)} {L T n : ℕ}
    {G : ℕ → Tracked H T → Prop} {s : Tracked H T} (hs : Valid H L n s) (hn : n < T)
    (hr : Ready H L s.chosen) (hg : s.running = true ∧ G n s)
    (w f : ℕ → ℝ) (j : Fin 3) (u : α) :
    (GreedyTrackedState.kernel H L T G n).avg
      (fun z => weightedError w f z j u-weightedError w f s j u) s =
      (w (n+1)*survivalDrift H s.chosen (j.val+2) u+
        (safeChoices H s.chosen u).card*offset w f n s j u)/(available H s.chosen).card := by
  classical
  rw [kernel_avg_ready G s hr]
  rw [sum_congr rfl (fun v _ => weighted_increment hs hn hr hg w f j u v),← sum_filter]
  change (∑ v ∈ safeChoices H s.chosen u,
      (w (n+1)*(((incident H (insert v s.chosen) (j.val+2) u).card:ℝ)-
        (incident H s.chosen (j.val+2) u).card)+offset w f n s j u))/_ = _
  rw [sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul]
  rfl

lemma weighted_drift_frozen {H : Finset (Finset α)} {L T n : ℕ}
    {G : ℕ → Tracked H T → Prop} {s : Tracked H T}
    (hg : ¬(s.running = true ∧ G n s)) (w f : ℕ → ℝ) (j : Fin 3) (u : α) :
    (GreedyTrackedState.kernel H L T G n).avg
      (fun z => weightedError w f z j u-weightedError w f s j u) s = 0 := by
  calc
    _ = (GreedyTrackedState.kernel H L T G n).avg (fun _ => 0) s := by
      apply Kernel.avg_congr_support
      intro z hz
      obtain ⟨a,ha,rfl⟩ := (GreedyTrackedState.kernel_support H L T G n s z).mp hz
      exact weighted_increment_frozen hg w f j u a
    _ = _ := Kernel.avg_const _ _ _

/-- Exact safe-choice second moment for the weighted observable. -/
theorem weighted_second_moment {H : Finset (Finset α)} {L T n : ℕ}
    {G : ℕ → Tracked H T → Prop} {s : Tracked H T} (hs : Valid H L n s) (hn : n < T)
    (hr : Ready H L s.chosen) (hg : s.running = true ∧ G n s)
    (w f : ℕ → ℝ) (j : Fin 3) (u : α) :
    (GreedyTrackedState.kernel H L T G n).avg
      (fun z => (weightedError w f z j u-weightedError w f s j u)^2) s =
      (∑ v ∈ safeChoices H s.chosen u,
        (w (n+1)*(((incident H (insert v s.chosen) (j.val+2) u).card:ℝ)-
          (incident H s.chosen (j.val+2) u).card)+offset w f n s j u)^2)/
        (available H s.chosen).card := by
  classical
  rw [kernel_avg_ready G s hr]
  have he (v : α) :
      (weightedError w f (update H T G n s (some v)) j u-weightedError w f s j u)^2 =
      if u ∈ available H (insert v s.chosen) then
        (w (n+1)*(((incident H (insert v s.chosen) (j.val+2) u).card:ℝ)-
          (incident H s.chosen (j.val+2) u).card)+offset w f n s j u)^2 else 0 := by
    rw [weighted_increment hs hn hr hg w f j u v]
    split <;> simp
  rw [sum_congr rfl (fun v _ => he v),← sum_filter]
  rfl

/-- Weighted second moments can use the existing NONLINEAR raw-variance
numerator. No linearity hypothesis is present in this transfer. -/
theorem weighted_variance_bound {H : Finset (Finset α)} {L T n : ℕ}
    {G : ℕ → Tracked H T → Prop} {s : Tracked H T} (hs : Valid H L n s) (hn : n < T)
    (hr : Ready H L s.chosen) (hg : s.running = true ∧ G n s)
    (w f : ℕ → ℝ) (j : Fin 3) (u : α) (V : ℝ)
    (hV : (∑ v ∈ safeChoices H s.chosen u,
      (((incident H (insert v s.chosen) (j.val+2) u).card:ℝ)-
        (incident H s.chosen (j.val+2) u).card)^2) ≤ V) :
    (GreedyTrackedState.kernel H L T G n).avg
      (fun z => (weightedError w f z j u-weightedError w f s j u)^2) s ≤
      2*(w (n+1))^2*V/(available H s.chosen).card+2*(offset w f n s j u)^2 := by
  rw [weighted_second_moment hs hn hr hg w f j u]
  have hsum : (∑ v ∈ safeChoices H s.chosen u,
      (w (n+1)*(((incident H (insert v s.chosen) (j.val+2) u).card:ℝ)-
        (incident H s.chosen (j.val+2) u).card)+offset w f n s j u)^2) ≤
      2*(w (n+1))^2*V+(available H s.chosen).card*(2*(offset w f n s j u)^2) := by
    calc
      _ ≤ ∑ v ∈ safeChoices H s.chosen u,
          (2*(w (n+1))^2*(((incident H (insert v s.chosen) (j.val+2) u).card:ℝ)-
            (incident H s.chosen (j.val+2) u).card)^2+2*(offset w f n s j u)^2) := by
        apply sum_le_sum
        intro v hv
        nlinarith only [sq_nonneg (w (n+1)*(((incident H (insert v s.chosen) (j.val+2) u).card:ℝ)-
          (incident H s.chosen (j.val+2) u).card)-offset w f n s j u)]
      _ = 2*(w (n+1))^2*(∑ v ∈ safeChoices H s.chosen u,
          (((incident H (insert v s.chosen) (j.val+2) u).card:ℝ)-
            (incident H s.chosen (j.val+2) u).card)^2)+
          (safeChoices H s.chosen u).card*(2*(offset w f n s j u)^2) := by
        rw [sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hV (by positivity))
        (mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card (filter_subset
          (fun v => u ∈ available H (insert v s.chosen)) (available H s.chosen))) (by positivity))
  have hQ : (0:ℝ) < (available H s.chosen).card := by
    exact_mod_cast card_pos.mpr hr.2
  calc
    _ ≤ (2*(w (n+1))^2*V+(available H s.chosen).card*(2*(offset w f n s j u)^2))/
        (available H s.chosen).card := div_le_div_of_nonneg_right hsum hQ.le
    _ = _ := by field_simp

#print axioms weightedError_eq_live
#print axioms weighted_increment
#print axioms weighted_increment_frozen
#print axioms weighted_drift
#print axioms weighted_drift_frozen
#print axioms weighted_second_moment
#print axioms weighted_variance_bound
end
end Erdos773.GreedyWeightedRecords
