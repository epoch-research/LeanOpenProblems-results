import Submission.GreedyTrackedMoments

/-!
Conditional second-moment bounds for the frozen local degree records.
These are finite one-step estimates, not integrated variance budgets or
long-time trajectory tracking.
-/
namespace Erdos773.GreedyTrackedVariance
open Finset GreedyHypergraphState StoppedGreedyMoments GreedyFiniteKernel
open FiniteKernelCrossing GreedyTrackedState GreedyTrackedMoments
open GreedyLinearDrift GreedyLinearLocal GreedyLinearHigherDrift GreedyCommonNeighbors
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
lemma square_le_variation (x p l B : ℝ) (hp : 0 ≤ p) (hl : 0 ≤ l)
    (hb : 0 ≤ B) (hbalance : x+l = p) (hx : |x| ≤ B) : x^2 ≤ B*(p+l) := by
  have habs : |x| ≤ p+l := abs_le.mpr ⟨by linarith,by linarith⟩
  calc
    x^2 = |x| * |x| := by rw [← pow_two,sq_abs]
    _ ≤ _ := mul_le_mul hx habs (abs_nonneg x) hb

/-- The sum of squared safe increments is controlled by total local variation.
    It does not charge B² for every possible choice. -/
theorem local_second_moment_bound {H : Finset (Finset α)} (hlin : Linear H)
    (I : Finset α) (j : ℕ) (hj : 2 ≤ j) (u : α) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ w ∈ safeChoices H I u,
      |((incident H (insert w I) j u).card:ℝ)-(incident H I j u).card| ≤ B) :
    (∑ w ∈ safeChoices H I u,
      (((incident H (insert w I) j u).card:ℝ)-(incident H I j u).card)^2) ≤
        B*((j:ℝ)*(incident H I (j+1) u).card+
          (∑ w ∈ safeChoices H I u, ((localLost H I j u w).card:ℝ))) := by
  have hp (w : α) (hw : w ∈ safeChoices H I u) :
      (((incident H (insert w I) j u).card:ℝ)-(incident H I j u).card)^2 ≤
        B*((localPromoted H I j u w).card+(localLost H I j u w).card) := by
    obtain ⟨hw0,hu⟩ := mem_filter.mp hw
    have huw : u ≠ w := by intro h; exact (mem_available.mp hu).1 (by simp [h])
    have hb := incident_card_step hw0 huw j
    have hbR : ((incident H (insert w I) j u).card:ℝ)+(localLost H I j u w).card =
        (incident H I j u).card+(localPromoted H I j u w).card := by exact_mod_cast hb
    exact square_le_variation _ _ _ B (by positivity) (by positivity) hB
      (by linarith) (hbound w hw)
  have hpSum : (∑ w ∈ safeChoices H I u, ((localPromoted H I j u w).card:ℝ)) =
      (j:ℝ)*(incident H I (j+1) u).card := by exact_mod_cast sum_localPromoted hlin I j hj u
  calc
    _ ≤ ∑ w ∈ safeChoices H I u,
        B*((localPromoted H I j u w).card+(localLost H I j u w).card) := sum_le_sum hp
    _ = _ := by rw [← mul_sum,sum_add_distrib,hpSum]

lemma localLost_two_sum_le {H : Finset (Finset α)} (hlin : Linear H)
    {I : Finset α} {u : α} (hu : u ∈ available H I) (h : ℝ)
    (hh : ∀ x ∈ closes H I u, ((incident H I 2 x).card:ℝ) ≤ h) :
    (∑ w ∈ safeChoices H I u, ((localLost H I 2 u w).card:ℝ)) ≤ h*(incident H I 2 u).card := by
  have hbalance := common_sum_balance hu
  have hle : (∑ w ∈ safeChoices H I u, commonDegree H I u w) ≤
      ∑ x ∈ closes H I u, (closes H I x).card := by omega
  calc
    _ = ∑ w ∈ safeChoices H I u, (commonDegree H I u w:ℝ) := by
      apply sum_congr rfl
      intro w hw
      obtain ⟨hw,hu⟩ := mem_filter.mp hw
      rw [localLost_two_card hlin hw hu]
    _ ≤ ∑ x ∈ closes H I u, ((closes H I x).card:ℝ) := by exact_mod_cast hle
    _ = ∑ x ∈ closes H I u, ((incident H I 2 x).card:ℝ) := by
      apply sum_congr rfl
      intro x hx
      rw [hlin.incident_two_card I x (closes_subset H I u hx)]
    _ ≤ ∑ _x ∈ closes H I u, h := sum_le_sum hh
    _ = _ := by simp [hlin.incident_two_card I u hu,mul_comm]

lemma localLost_higher_sum_le {H : Finset (Finset α)} (hlin : Linear H)
    (I : Finset α) (j : ℕ) (hj : 3 ≤ j) (u : α) (h : ℝ)
    (hh : ∀ x ∈ available H I, ((incident H I 2 x).card:ℝ) ≤ h) :
    (∑ w ∈ safeChoices H I u, ((localLost H I j u w).card:ℝ)) ≤
      (j-1:ℕ)*(h+1)*(incident H I j u).card := by
  have hC : ∀ x ∈ available H I, ∀ y ∈ available H I, x ≠ y → commonDegree H I x y ≤ Fintype.card α := by
    intro x hx y hy hxy
    exact card_le_univ _
  have hle := (sum_localLost_bounds hlin I j hj u (Fintype.card α) hC).1
  have hleR : (∑ w ∈ safeChoices H I u, ((localLost H I j u w).card:ℝ)) ≤
      (j-1:ℕ)*(incident H I j u).card+(neighborWeight H I j u:ℝ) := by exact_mod_cast hle
  have hw := (neighborWeight_bounds hlin I j u 0 h (fun _ _ => by positivity) hh).2
  nlinarith

/-- Two-degree second moments use the small common-neighbor increment cap. -/
theorem local_two_second_moment {H : Finset (Finset α)} (hlin : Linear H)
    {I : Finset α} {u : α} (hu : u ∈ available H I) (h : ℝ) (C : ℕ)
    (hh : ∀ x ∈ closes H I u, ((incident H I 2 x).card:ℝ) ≤ h)
    (hC : ∀ w ∈ available H I, u ≠ w → commonDegree H I u w ≤ C) :
    (∑ w ∈ safeChoices H I u,
      (((incident H (insert w I) 2 u).card:ℝ)-(incident H I 2 u).card)^2) ≤
        ((C:ℝ)+1)*(2*(incident H I 3 u).card+h*(incident H I 2 u).card) := by
  have hb (w : α) (hw : w ∈ safeChoices H I u) :
      |((incident H (insert w I) 2 u).card:ℝ)-(incident H I 2 u).card| ≤ (C:ℝ)+1 := by
    obtain ⟨hw,hu'⟩ := mem_filter.mp hw
    have huw : u ≠ w := by intro hh; exact (mem_available.mp hu').1 (by simp [hh])
    exact incident_two_increment_bound hlin hw hu' C (hC w hw huw)
  have hfirst := local_second_moment_bound hlin I 2 (by omega) u ((C:ℝ)+1) (by positivity) hb
  norm_num only [Nat.cast_ofNat] at hfirst
  apply hfirst.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add le_rfl (localLost_two_sum_le hlin hu h hh)

/-- Higher degrees use the available two-degree cap for increments, and the
    actual promotion/loss totals for conditional variation. -/
theorem local_higher_second_moment {H : Finset (Finset α)} (hlin : Linear H)
    (I : Finset α) (j : ℕ) (hj : 3 ≤ j) (u : α) (h : ℝ) (hh0 : 0 ≤ h)
    (hh : ∀ x ∈ available H I, ((incident H I 2 x).card:ℝ) ≤ h) :
    (∑ w ∈ safeChoices H I u,
      (((incident H (insert w I) j u).card:ℝ)-(incident H I j u).card)^2) ≤
        (h+1)*((j:ℝ)*(incident H I (j+1) u).card+(j-1:ℕ)*(h+1)*(incident H I j u).card) := by
  have hb (w : α) (hw : w ∈ safeChoices H I u) :
      |((incident H (insert w I) j u).card:ℝ)-(incident H I j u).card| ≤ h+1 := by
    obtain ⟨hw,hu⟩ := mem_filter.mp hw
    have hi := incident_increment_bound hlin hw hu j
    rw [← hlin.incident_two_card I w hw] at hi
    exact hi.trans (add_le_add (hh w hw) le_rfl)
  apply (local_second_moment_bound hlin I j (by omega) u (h+1) (by positivity) hb).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add le_rfl (localLost_higher_sum_le hlin I j hj u h hh)

/-- Conditional second moment of the actual recorded two-degree. -/
theorem recorded_two_second_moment {H : Finset (Finset α)} (hlin : Linear H)
    {L T n : ℕ} {G : ℕ → Tracked H T → Prop} {s : Tracked H T}
    (hs : Coherent H s) (hr : Ready H L s.chosen) (hg : s.running = true ∧ G n s)
    {u : α} (hu : u ∈ available H s.chosen) (h : ℝ) (C : ℕ)
    (hh : ∀ x ∈ closes H s.chosen u, ((incident H s.chosen 2 x).card:ℝ) ≤ h)
    (hC : ∀ w ∈ available H s.chosen, u ≠ w → commonDegree H s.chosen u w ≤ C) :
    (GreedyTrackedState.kernel H L T G n).avg (fun z => (degree z 0 u-degree s 0 u)^2) s ≤
      (((C:ℝ)+1)*(2*(incident H s.chosen 3 u).card+h*(incident H s.chosen 2 u).card))/
        (available H s.chosen).card := by
  rw [degree_second_moment hs hr hg]
  exact div_le_div_of_nonneg_right (local_two_second_moment hlin hu h C hh hC) (by positivity)

/-- Conditional second moment of each actual recorded higher degree. -/
theorem recorded_higher_second_moment {H : Finset (Finset α)} (hlin : Linear H)
    {L T n : ℕ} {G : ℕ → Tracked H T → Prop} {s : Tracked H T}
    (hs : Coherent H s) (hr : Ready H L s.chosen) (hg : s.running = true ∧ G n s)
    (j : Fin 3) (hj : 1 ≤ j.val) (u : α) (h : ℝ) (hh0 : 0 ≤ h)
    (hh : ∀ x ∈ available H s.chosen, ((incident H s.chosen 2 x).card:ℝ) ≤ h) :
    (GreedyTrackedState.kernel H L T G n).avg (fun z => (degree z j u-degree s j u)^2) s ≤
      ((h+1)*((j.val+2:ℕ)*(incident H s.chosen (j.val+3) u).card+
        (j.val+1:ℕ)*(h+1)*(incident H s.chosen (j.val+2) u).card))/(available H s.chosen).card := by
  rw [degree_second_moment hs hr hg]
  have hb := local_higher_second_moment hlin s.chosen (j.val+2) (by omega) u h hh0 hh
  convert div_le_div_of_nonneg_right hb (by positivity : (0:ℝ) ≤ (available H s.chosen).card) using 1

/-- A supplied raw-increment cap transfers to the profile error with exactly
    the absolute one-step profile change added. -/
theorem profile_increment_bound {H : Finset (Finset α)}
    {L T n : ℕ} {G : ℕ → Tracked H T → Prop} {s : Tracked H T}
    (hs : Valid H L n s) (hn : n < T) (hr : Ready H L s.chosen)
    (hg : s.running = true ∧ G n s) (f : ℕ → ℝ) (j : Fin 3) (u : α) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ w ∈ safeChoices H s.chosen u,
      |((incident H (insert w s.chosen) (j.val+2) u).card:ℝ)-(incident H s.chosen (j.val+2) u).card| ≤ B)
    {z : Tracked H T} (hz : 0 < (GreedyTrackedState.kernel H L T G n).weight s z) :
    |error f z j u-error f s j u| ≤ B+|f (n+1)-f n| := by
  classical
  obtain ⟨a,ha,rfl⟩ := (GreedyTrackedState.kernel_support H L T G n s z).mp hz
  cases a with
  | none => simp only [update_none,sub_self,abs_zero]; positivity
  | some w =>
    obtain ⟨_,hw⟩ := (mem_actions_some H L s.chosen w).mp ha
    rw [error_increment hs hn hr hg f j u w]
    by_cases hu : u ∈ available H (insert w s.chosen)
    · rw [if_pos hu]
      exact (abs_sub _ _).trans (add_le_add (hb w (mem_filter.mpr ⟨hw,hu⟩)) le_rfl)
    · rw [if_neg hu,abs_zero]
      positivity

#print axioms local_second_moment_bound
#print axioms local_two_second_moment
#print axioms local_higher_second_moment
#print axioms recorded_two_second_moment
#print axioms recorded_higher_second_moment
#print axioms profile_increment_bound
end
end Erdos773.GreedyTrackedVariance
