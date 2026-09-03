import Submission.GreedyTrackedVariance
import Submission.GreedyCodegreeTwoDrift

/-!
Nonlinear conditional second-moment bounds for the frozen local degree records.
These are finite one-step estimates, not integrated variance budgets or
long-time trajectory tracking.
-/
namespace Erdos773.GreedyCodegreeVariance
open Finset GreedyHypergraphState StoppedGreedyMoments GreedyFiniteKernel
open FiniteKernelCrossing GreedyTrackedState GreedyTrackedMoments
open GreedyLinearDrift GreedyLinearLocal GreedyLinearHigherDrift GreedyCommonNeighbors
open GreedyCodegreeLocal GreedyCodegreeDrift GreedyCodegreeTwoDrift
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The sum of squared safe increments is controlled by total local variation.
    It does not charge B² for every possible choice. -/
theorem local_second_moment_bound {H : Finset (Finset α)}
    (I : Finset α) (j : ℕ) (u : α) (B : ℝ) (hB : 0 ≤ B)
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
    exact GreedyTrackedVariance.square_le_variation _ _ _ B (by positivity) (by positivity) hB
      (by linarith) (hbound w hw)
  have hpSum : (∑ w ∈ safeChoices H I u, ((localPromoted H I j u w).card:ℝ)) ≤
      (j:ℝ)*(incident H I (j+1) u).card := by
    have hbal := GreedyCodegreeDrift.sum_localPromoted H I j u
    exact_mod_cast (show (∑ w ∈ safeChoices H I u, (localPromoted H I j u w).card) ≤
      j*(incident H I (j+1) u).card by omega)
  calc
    _ ≤ ∑ w ∈ safeChoices H I u,
        B*((localPromoted H I j u w).card+(localLost H I j u w).card) := sum_le_sum hp
    _ = B*((∑ w ∈ safeChoices H I u, ((localPromoted H I j u w).card:ℝ))+
        (∑ w ∈ safeChoices H I u, ((localLost H I j u w).card:ℝ))) := by rw [← mul_sum,sum_add_distrib]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hpSum le_rfl) hB

/-- Multiplicity-weighted loss is still bounded by h*d₂, not K*h*d₂. -/
lemma localLost_two_sum_le {H : Finset (Finset α)}
    {I : Finset α} {u : α} (hu : u ∈ available H I) (h : ℝ)
    (hh : ∀ x ∈ closes H I u, ((incident H I 2 x).card:ℝ) ≤ h) :
    (∑ w ∈ safeChoices H I u, ((localLost H I 2 u w).card:ℝ)) ≤ h*(incident H I 2 u).card := by
  have he : (∑ w ∈ safeChoices H I u, ((localLost H I 2 u w).card:ℝ)) =
      ∑ x ∈ closes H I u, ((pairReps H I u x).card:ℝ)*(restrictedClosure H I u x).card := by
    exact_mod_cast sum_localLost_two I u
  have hw : (∑ x ∈ closes H I u, ((pairReps H I u x).card:ℝ)) = (incident H I 2 u).card := by
    exact_mod_cast (incident_two_card hu).symm
  rw [he]
  calc
    _ ≤ ∑ x ∈ closes H I u, ((pairReps H I u x).card:ℝ)*h := by
      apply sum_le_sum
      intro x hx
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hc : ((restrictedClosure H I u x).card:ℝ) ≤ (incident H I 2 x).card := by
        exact_mod_cast (card_le_card inter_subset_left).trans
          (closes_card_le_incident (closes_subset H I u hx))
      exact hc.trans (hh x hx)
    _ = _ := by rw [← sum_mul,hw,mul_comm]

lemma neighborWeight_le {H : Finset (Finset α)}
    (I : Finset α) (j : ℕ) (u : α) (h : ℝ)
    (hh : ∀ x ∈ available H I, ((incident H I 2 x).card:ℝ) ≤ h) :
    (neighborWeight H I j u:ℝ) ≤ h*(j-1:ℕ)*(incident H I j u).card := by
  have hc (e : Finset α) (he : e ∈ incident H I j u) : ((e \ I).erase u).card = j-1 := by
    obtain ⟨he,hu⟩ := mem_filter.mp he
    rw [card_erase_of_mem hu,(mem_filter.mp he).2.2]
  have hw : (neighborWeight H I j u:ℝ) =
      ∑ e ∈ incident H I j u, ∑ x ∈ (e \ I).erase u, ((closes H I x).card:ℝ) := by
    unfold neighborWeight
    push_cast
    rfl
  rw [hw]
  calc
    _ ≤ ∑ e ∈ incident H I j u, ∑ _x ∈ (e \ I).erase u, h := by
      apply sum_le_sum
      intro e he
      apply sum_le_sum
      intro x hx
      have hxa := (mem_incident.mp he).2.1 (mem_erase.mp hx).2
      have hc : ((closes H I x).card:ℝ) ≤ (incident H I 2 x).card := by
        exact_mod_cast closes_card_le_incident hxa
      exact hc.trans (hh x hxa)
    _ = _ := by
      rw [sum_congr rfl (fun e he => show (∑ _x ∈ (e \ I).erase u, h) = (j-1:ℕ)*h by simp [hc e he])]
      simp [mul_comm]

lemma localLost_higher_sum_le {H : Finset (Finset α)}
    (I : Finset α) (j : ℕ) (hj : 3 ≤ j) (u : α) (h : ℝ)
    (hh : ∀ x ∈ available H I, ((incident H I 2 x).card:ℝ) ≤ h) :
    (∑ w ∈ safeChoices H I u, ((localLost H I j u w).card:ℝ)) ≤
      (j-1:ℕ)*(h+1)*(incident H I j u).card := by
  have hC : ∀ x ∈ available H I, ∀ y ∈ available H I, x ≠ y → commonDegree H I x y ≤ Fintype.card α := by
    intro x hx y hy hxy
    exact card_le_univ _
  have hle := (GreedyCodegreeHigherDrift.sum_localLost_bounds I j hj u (Fintype.card α) hC).1
  have hleR : (∑ w ∈ safeChoices H I u, ((localLost H I j u w).card:ℝ)) ≤
      (j-1:ℕ)*(incident H I j u).card+(neighborWeight H I j u:ℝ) := by exact_mod_cast hle
  have hw := neighborWeight_le I j u h hh
  nlinarith only [hleR,hw]

/-- Two-degree second moments use the small common-neighbor increment cap. -/
theorem local_two_second_moment {H : Finset (Finset α)} (K : ℕ)
    (hK : ∀ a b : α, a ≠ b → FourUniformRegularization.pairDegree H a b ≤ K)
    {I : Finset α} {u : α} (hu : u ∈ available H I) (h : ℝ) (C E : ℕ)
    (hh : ∀ x ∈ closes H I u, ((incident H I 2 x).card:ℝ) ≤ h)
    (hC : ∀ w ∈ available H I, u ≠ w → commonDegree H I u w ≤ C)
    (hE : duplicateExcess H I u ≤ E) :
    (∑ w ∈ safeChoices H I u,
      (((incident H (insert w I) 2 u).card:ℝ)-(incident H I 2 u).card)^2) ≤
        ((K:ℝ)+C+E)*(2*(incident H I 3 u).card+h*(incident H I 2 u).card) := by
  have hb (w : α) (hw : w ∈ safeChoices H I u) :
      |((incident H (insert w I) 2 u).card:ℝ)-(incident H I 2 u).card| ≤ (K:ℝ)+C+E := by
    obtain ⟨hw,hu'⟩ := mem_filter.mp hw
    have huw : u ≠ w := by intro hh; exact (mem_available.mp hu').1 (by simp [hh])
    exact GreedyCodegreeLocal.incident_two_increment_bound K hK hw hu' C E (hC w hw huw) hE
  have hfirst := local_second_moment_bound I 2 u ((K:ℝ)+C+E) (by positivity) hb
  norm_num only [Nat.cast_ofNat] at hfirst
  apply hfirst.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add le_rfl (localLost_two_sum_le hu h hh)

/-- Higher degrees use the available two-degree cap for increments, and the
    actual promotion/loss totals for conditional variation. -/
theorem local_higher_second_moment {H : Finset (Finset α)} (K : ℕ)
    (hK : ∀ a b : α, a ≠ b → FourUniformRegularization.pairDegree H a b ≤ K)
    (I : Finset α) (j : ℕ) (hj : 3 ≤ j) (u : α) (h : ℝ) (hh0 : 0 ≤ h)
    (hh : ∀ x ∈ available H I, ((incident H I 2 x).card:ℝ) ≤ h) :
    (∑ w ∈ safeChoices H I u,
      (((incident H (insert w I) j u).card:ℝ)-(incident H I j u).card)^2) ≤
        (K:ℝ)*(h+1)*((j:ℝ)*(incident H I (j+1) u).card+(j-1:ℕ)*(h+1)*(incident H I j u).card) := by
  have hb (w : α) (hw : w ∈ safeChoices H I u) :
      |((incident H (insert w I) j u).card:ℝ)-(incident H I j u).card| ≤ (K:ℝ)*(h+1) := by
    obtain ⟨hw,hu⟩ := mem_filter.mp hw
    have hi := GreedyCodegreeLocal.incident_increment_bound K hK hw hu j
    have hc : ((closes H I w).card:ℝ) ≤ (incident H I 2 w).card := by
      exact_mod_cast closes_card_le_incident hw
    exact hi.trans (mul_le_mul_of_nonneg_left (add_le_add (hc.trans (hh w hw)) le_rfl) (by positivity))
  apply (local_second_moment_bound I j u ((K:ℝ)*(h+1)) (by positivity) hb).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add le_rfl (localLost_higher_sum_le I j hj u h hh)

/-- Conditional second moment of the actual recorded two-degree. -/
theorem recorded_two_second_moment {H : Finset (Finset α)} (K : ℕ)
    (hK : ∀ a b : α, a ≠ b → FourUniformRegularization.pairDegree H a b ≤ K)
    {L T n : ℕ} {G : ℕ → Tracked H T → Prop} {s : Tracked H T}
    (hs : Coherent H s) (hr : Ready H L s.chosen) (hg : s.running = true ∧ G n s)
    {u : α} (hu : u ∈ available H s.chosen) (h : ℝ) (C E : ℕ)
    (hh : ∀ x ∈ closes H s.chosen u, ((incident H s.chosen 2 x).card:ℝ) ≤ h)
    (hC : ∀ w ∈ available H s.chosen, u ≠ w → commonDegree H s.chosen u w ≤ C)
    (hE : duplicateExcess H s.chosen u ≤ E) :
    (GreedyTrackedState.kernel H L T G n).avg (fun z => (degree z 0 u-degree s 0 u)^2) s ≤
      (((K:ℝ)+C+E)*(2*(incident H s.chosen 3 u).card+h*(incident H s.chosen 2 u).card))/
        (available H s.chosen).card := by
  rw [degree_second_moment hs hr hg]
  exact div_le_div_of_nonneg_right (local_two_second_moment K hK hu h C E hh hC hE) (by positivity)

/-- Conditional second moment of each actual recorded higher degree. -/
theorem recorded_higher_second_moment {H : Finset (Finset α)} (K : ℕ)
    (hK : ∀ a b : α, a ≠ b → FourUniformRegularization.pairDegree H a b ≤ K)
    {L T n : ℕ} {G : ℕ → Tracked H T → Prop} {s : Tracked H T}
    (hs : Coherent H s) (hr : Ready H L s.chosen) (hg : s.running = true ∧ G n s)
    (j : Fin 3) (hj : 1 ≤ j.val) (u : α) (h : ℝ) (hh0 : 0 ≤ h)
    (hh : ∀ x ∈ available H s.chosen, ((incident H s.chosen 2 x).card:ℝ) ≤ h) :
    (GreedyTrackedState.kernel H L T G n).avg (fun z => (degree z j u-degree s j u)^2) s ≤
      ((K:ℝ)*(h+1)*((j.val+2:ℕ)*(incident H s.chosen (j.val+3) u).card+
        (j.val+1:ℕ)*(h+1)*(incident H s.chosen (j.val+2) u).card))/(available H s.chosen).card := by
  rw [degree_second_moment hs hr hg]
  have hb := local_higher_second_moment K hK s.chosen (j.val+2) (by omega) u h hh0 hh
  convert div_le_div_of_nonneg_right hb (by positivity : (0:ℝ) ≤ (available H s.chosen).card) using 1

#print axioms local_second_moment_bound
#print axioms local_two_second_moment
#print axioms local_higher_second_moment
#print axioms recorded_two_second_moment
#print axioms recorded_higher_second_moment
#print axioms localLost_two_sum_le
#print axioms neighborWeight_le
#print axioms localLost_higher_sum_le
end
end Erdos773.GreedyCodegreeVariance
