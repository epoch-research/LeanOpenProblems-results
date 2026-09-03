import Submission.GreedyTrackedState

/-!
One-step moments for the concrete frozen-degree records. Profile increments
are subtracted only on safe updates, including the survival-probability
factor. No typical-profile or integrated variance assertion is made.
-/
namespace Erdos773.GreedyTrackedMoments
open Finset GreedyHypergraphState StoppedGreedyMoments GreedyFiniteKernel
open FiniteKernelCrossing FiniteKernelChoices GreedyTrackedState
open GreedyLinearDrift GreedyLinearLocal GreedyLinearHigherDrift GreedyCommonNeighbors
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev degree {H : Finset (Finset α)} {T : ℕ} (s : Tracked H T) (j : Fin 3) (u : α) : ℝ :=
  (s.counts j u).val

def error {H : Finset (Finset α)} {T : ℕ} (f : ℕ → ℝ) (s : Tracked H T) (j : Fin 3) (u : α) : ℝ :=
  degree s j u-f (s.clock u).val

/-- On a live available vertex, the stored error is the actual local degree
    minus the current-time profile, not a stale profile value. -/
lemma error_eq_live {H : Finset (Finset α)} {L T n : ℕ} {s : Tracked H T}
    (hs : Valid H L n s) (hrun : s.running = true) (hr : Ready H L s.chosen)
    (f : ℕ → ℝ) (j : Fin 3) {u : α} (hu : u ∈ available H s.chosen) :
    error f s j u = ((incident H s.chosen (j.val+2) u).card:ℝ)-f n := by
  unfold error degree
  rw [hs.1 hrun u hu j,hs.2.2 hrun hr u hu]

lemma live_degree_bounds {H : Finset (Finset α)} {L T n : ℕ} {s : Tracked H T}
    (hs : Valid H L n s) (hrun : s.running = true) (hr : Ready H L s.chosen)
    (f : ℕ → ℝ) (j : Fin 3) {u : α} (hu : u ∈ available H s.chosen)
    (l h : ℝ) (he : l-f n ≤ error f s j u ∧ error f s j u ≤ h-f n) :
    l ≤ ((incident H s.chosen (j.val+2) u).card:ℝ) ∧
      ((incident H s.chosen (j.val+2) u).card:ℝ) ≤ h := by
  rw [error_eq_live hs hrun hr f j hu] at he
  constructor <;> linarith only [he.1,he.2]

lemma kernel_avg_ready {H : Finset (Finset α)} {L T n : ℕ}
    (G : ℕ → Tracked H T → Prop) (s : Tracked H T) (hr : Ready H L s.chosen)
    (f : Tracked H T → ℝ) :
    (GreedyTrackedState.kernel H L T G n).avg f s =
      (∑ w ∈ available H s.chosen, f (update H T G n s (some w)))/(available H s.chosen).card := by
  classical
  rw [GreedyTrackedState.kernel,liftedKernel,ofChoices_avg]
  unfold actions
  rw [if_pos hr,card_image_of_injective _ (Option.some_injective α)]
  rw [sum_image (fun a _ b _ hab => Option.some.inj hab)]

lemma kernel_avg_not_ready {H : Finset (Finset α)} {L T n : ℕ}
    (G : ℕ → Tracked H T → Prop) (s : Tracked H T) (hr : ¬Ready H L s.chosen)
    (f : Tracked H T → ℝ) : (GreedyTrackedState.kernel H L T G n).avg f s = f s := by
  classical
  rw [GreedyTrackedState.kernel,liftedKernel,ofChoices_avg]
  simp [actions,hr]

lemma kernel_eq_of_not_ready {H : Finset (Finset α)} {L T n : ℕ}
    {G : ℕ → Tracked H T → Prop} {s z : Tracked H T} (hr : ¬Ready H L s.chosen)
    (hz : 0 < (GreedyTrackedState.kernel H L T G n).weight s z) : z = s := by
  obtain ⟨a,ha,rfl⟩ := (GreedyTrackedState.kernel_support H L T G n s z).mp hz
  cases a with
  | none => rfl
  | some w => exact (hr ((mem_actions_some H L s.chosen w).mp ha).1).elim

lemma degree_increment {H : Finset (Finset α)} {T n : ℕ}
    {G : ℕ → Tracked H T → Prop} {s : Tracked H T} (hs : Coherent H s)
    (hg : s.running = true ∧ G n s) (j : Fin 3) (u w : α) :
    degree (update H T G n s (some w)) j u-degree s j u =
      if u ∈ available H (insert w s.chosen) then
        ((incident H (insert w s.chosen) (j.val+2) u).card:ℝ)-(incident H s.chosen (j.val+2) u).card
      else 0 := by
  classical
  by_cases hu : u ∈ available H (insert w s.chosen)
  · have hu0 := available_antitone (subset_insert w s.chosen) hu
    simp only [degree,update,if_pos hg,if_pos hu,boundedDegree]
    rw [hs hg.1 u hu0 j]
  · simp [degree,update,hg,hu]

lemma error_increment {H : Finset (Finset α)} {L T n : ℕ}
    {G : ℕ → Tracked H T → Prop} {s : Tracked H T} (hs : Valid H L n s) (hn : n < T)
    (hr : Ready H L s.chosen) (hg : s.running = true ∧ G n s)
    (f : ℕ → ℝ) (j : Fin 3) (u w : α) :
    error f (update H T G n s (some w)) j u-error f s j u =
      if u ∈ available H (insert w s.chosen) then
        ((incident H (insert w s.chosen) (j.val+2) u).card:ℝ)-(incident H s.chosen (j.val+2) u).card-
          (f (n+1)-f n) else 0 := by
  classical
  by_cases hu : u ∈ available H (insert w s.chosen)
  · have hu0 := available_antitone (subset_insert w s.chosen) hu
    have hclock := hs.2.2 hg.1 hr u hu0
    have hdegree := hs.1 hg.1 u hu0 j
    simp only [error,degree,update,if_pos hg,if_pos hu,boundedDegree,clockAt]
    rw [min_eq_left (by omega : n+1 ≤ T),hclock,hdegree]
    ring
  · simp [error,degree,update,hg,hu]

lemma degree_increment_frozen {H : Finset (Finset α)} {T n : ℕ}
    {G : ℕ → Tracked H T → Prop} {s : Tracked H T}
    (hg : ¬(s.running = true ∧ G n s)) (j : Fin 3) (u : α) (a : Option α) :
    degree (update H T G n s a) j u-degree s j u = 0 := by
  classical
  cases a <;> simp [degree,update,hg]

lemma error_increment_frozen {H : Finset (Finset α)} {T n : ℕ}
    {G : ℕ → Tracked H T → Prop} {s : Tracked H T}
    (hg : ¬(s.running = true ∧ G n s)) (f : ℕ → ℝ) (j : Fin 3) (u : α) (a : Option α) :
    error f (update H T G n s a) j u-error f s j u = 0 := by
  classical
  cases a <;> simp [error,degree,update,hg]

/-- Inactive or guard-failed records have zero drift, even if the carrier
    continues to select vertices. -/
theorem error_drift_frozen {H : Finset (Finset α)} {L T n : ℕ}
    {G : ℕ → Tracked H T → Prop} {s : Tracked H T}
    (hg : ¬(s.running = true ∧ G n s)) (f : ℕ → ℝ) (j : Fin 3) (u : α) :
    (GreedyTrackedState.kernel H L T G n).avg (fun z => error f z j u-error f s j u) s = 0 := by
  calc
    _ = (GreedyTrackedState.kernel H L T G n).avg (fun _ => 0) s := by
      apply Kernel.avg_congr_support
      intro z hz
      obtain ⟨a,ha,rfl⟩ := (GreedyTrackedState.kernel_support H L T G n s z).mp hz
      exact error_increment_frozen hg f j u a
    _ = _ := Kernel.avg_const _ _ _

lemma error_second_moment_frozen {H : Finset (Finset α)} {L T n : ℕ}
    {G : ℕ → Tracked H T → Prop} {s : Tracked H T}
    (hg : ¬(s.running = true ∧ G n s)) (f : ℕ → ℝ) (j : Fin 3) (u : α) :
    (GreedyTrackedState.kernel H L T G n).avg (fun z => (error f z j u-error f s j u)^2) s = 0 := by
  calc
    _ = (GreedyTrackedState.kernel H L T G n).avg (fun _ => 0) s := by
      apply Kernel.avg_congr_support
      intro z hz
      obtain ⟨a,ha,rfl⟩ := (GreedyTrackedState.kernel_support H L T G n s z).mp hz
      rw [error_increment_frozen hg f j u a]
      norm_num
    _ = _ := Kernel.avg_const _ _ _

/-- The previously proved safe-choice local drift is the actual conditional
    mean of the recorded degree, divided by the available cardinality. -/
theorem degree_drift {H : Finset (Finset α)} {L T n : ℕ}
    {G : ℕ → Tracked H T → Prop} {s : Tracked H T} (hs : Coherent H s)
    (hr : Ready H L s.chosen) (hg : s.running = true ∧ G n s) (j : Fin 3) (u : α) :
    (GreedyTrackedState.kernel H L T G n).avg (fun z => degree z j u-degree s j u) s =
      survivalDrift H s.chosen (j.val+2) u/(available H s.chosen).card := by
  classical
  rw [kernel_avg_ready G s hr]
  rw [sum_congr rfl (fun w _ => degree_increment hs hg j u w),← sum_filter]
  rfl

/-- Mean increment of the profile error. The profile difference is weighted
    by the number of SAFE choices, not by the total number of choices. -/
theorem error_drift {H : Finset (Finset α)} {L T n : ℕ}
    {G : ℕ → Tracked H T → Prop} {s : Tracked H T} (hs : Valid H L n s) (hn : n < T)
    (hr : Ready H L s.chosen) (hg : s.running = true ∧ G n s)
    (f : ℕ → ℝ) (j : Fin 3) (u : α) :
    (GreedyTrackedState.kernel H L T G n).avg (fun z => error f z j u-error f s j u) s =
      (survivalDrift H s.chosen (j.val+2) u-
        (safeChoices H s.chosen u).card*(f (n+1)-f n))/(available H s.chosen).card := by
  classical
  rw [kernel_avg_ready G s hr]
  rw [sum_congr rfl (fun w _ => error_increment hs hn hr hg f j u w),← sum_filter]
  simp only [survivalDrift,safeChoices,sum_sub_distrib,sum_const,nsmul_eq_mul]
  ring

/-- The same safe-update rule gives the exact conditional second moment. -/
theorem degree_second_moment {H : Finset (Finset α)} {L T n : ℕ}
    {G : ℕ → Tracked H T → Prop} {s : Tracked H T} (hs : Coherent H s)
    (hr : Ready H L s.chosen) (hg : s.running = true ∧ G n s) (j : Fin 3) (u : α) :
    (GreedyTrackedState.kernel H L T G n).avg (fun z => (degree z j u-degree s j u)^2) s =
      (∑ w ∈ safeChoices H s.chosen u,
        (((incident H (insert w s.chosen) (j.val+2) u).card:ℝ)-
          (incident H s.chosen (j.val+2) u).card)^2)/(available H s.chosen).card := by
  classical
  rw [kernel_avg_ready G s hr]
  have he (w : α) : (degree (update H T G n s (some w)) j u-degree s j u)^2 =
      if u ∈ available H (insert w s.chosen) then
        (((incident H (insert w s.chosen) (j.val+2) u).card:ℝ)-
          (incident H s.chosen (j.val+2) u).card)^2 else 0 := by
    rw [degree_increment hs hg j u w]
    split_ifs <;> simp
  rw [sum_congr rfl (fun w _ => he w),← sum_filter]
  rfl

/-- Adding the deterministic profile slope costs only twice its square in
    the conditional second moment. Frozen choices cause no extra cost. -/
theorem error_second_moment {H : Finset (Finset α)} {L T n : ℕ}
    {G : ℕ → Tracked H T → Prop} {s : Tracked H T} (hs : Valid H L n s) (hn : n < T)
    (hr : Ready H L s.chosen) (hg : s.running = true ∧ G n s)
    (f : ℕ → ℝ) (j : Fin 3) (u : α) :
    (GreedyTrackedState.kernel H L T G n).avg (fun z => (error f z j u-error f s j u)^2) s ≤
      2*(GreedyTrackedState.kernel H L T G n).avg (fun z => (degree z j u-degree s j u)^2) s+
        2*(f (n+1)-f n)^2 := by
  have hpoint (z : Tracked H T) (hz : 0 < (GreedyTrackedState.kernel H L T G n).weight s z) :
      (error f z j u-error f s j u)^2 ≤ 2*(degree z j u-degree s j u)^2+2*(f (n+1)-f n)^2 := by
    classical
    obtain ⟨a,ha,rfl⟩ := (GreedyTrackedState.kernel_support H L T G n s z).mp hz
    cases a with
    | none => simp only [update_none,sub_self,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_add]; positivity
    | some w =>
      rw [error_increment hs hn hr hg f j u w,degree_increment hs.1 hg j u w]
      split_ifs
      · nlinarith only [sq_nonneg
          ((((incident H (insert w s.chosen) (j.val+2) u).card:ℝ)-
            (incident H s.chosen (j.val+2) u).card)+(f (n+1)-f n))]
      · simp only [zero_pow (by decide : 2 ≠ 0),mul_zero,zero_add]
        positivity
  calc
    _ ≤ (GreedyTrackedState.kernel H L T G n).avg
        (fun z => 2*(degree z j u-degree s j u)^2+2*(f (n+1)-f n)^2) s :=
      Kernel.avg_mono_support _ s hpoint
    _ = _ := by rw [Kernel.avg_add,Kernel.avg_mul,Kernel.avg_const]

#print axioms error_eq_live
#print axioms live_degree_bounds
#print axioms degree_increment
#print axioms error_increment
#print axioms error_drift_frozen
#print axioms degree_drift
#print axioms error_drift
#print axioms degree_second_moment
#print axioms error_second_moment
end
end Erdos773.GreedyTrackedMoments
