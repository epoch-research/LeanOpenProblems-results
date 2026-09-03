import Submission.FiniteMovingMean
import Submission.GreedyTwoDegreeEnergy
import Submission.GreedyHigherDegreeEnergy

/-!
Drift of the ACTUAL mean degrees of the available vertices. Vertex deaths
supply a second covariance term. The two-degree correction is a negative
variance, whereas higher mixed covariances have no presumed sign. Uniform
conditional drift is obtained only after an explicit reweighting error.
-/
namespace Erdos773.GreedyAvailableMeanDrift
open Finset GreedyHypergraphState GreedyLinearLocal GreedyCodegreeDrift
open GreedySurvivalTotalDrift FiniteMovingMean GreedyProfileDrift
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev localDegree (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (u : α) : ℝ :=
  (incident H I j u).card

def meanDegree (H : Finset (Finset α)) (I : Finset α) (j : ℕ) : ℝ :=
  mean (available H I) (localDegree H I j)

def covariance (H : Finset (Finset α)) (I : Finset α) (j k : ℕ) : ℝ :=
  ∑ u ∈ available H I,
    (localDegree H I j u-meanDegree H I j)*(localDegree H I k u-meanDegree H I k)

lemma meanDegree_card (H : Finset (Finset α)) (I : Finset α) (j : ℕ) :
    (available H I).card*meanDegree H I j = ∑ u ∈ available H I, localDegree H I j u :=
  card_mul_mean _ _

lemma covariance_self (H : Finset (Finset α)) (I : Finset α) (j : ℕ) :
    covariance H I j j =
      ∑ u ∈ available H I, (localDegree H I j u-meanDegree H I j)^2 := by
  simp only [covariance, pow_two]

lemma covariance_self_nonneg (H : Finset (Finset α)) (I : Finset α) (j : ℕ) :
    0 ≤ covariance H I j j := by rw [covariance_self]; positivity

/-- Exact additional centered death cost. -/
lemma death_covariance (H : Finset (Finset α)) (I : Finset α) (j : ℕ) :
    (∑ u ∈ available H I, (1+((closes H I u).card:ℝ))*
      (localDegree H I j u-meanDegree H I j)) = covariance H I j 2-
      (∑ u ∈ available H I, (duplicateExcess H I u:ℝ)*
        (localDegree H I j u-meanDegree H I j)) := by
  have he (u : α) (hu : u ∈ available H I) :
      (1+((closes H I u).card:ℝ))*(localDegree H I j u-meanDegree H I j) =
        (localDegree H I j u-meanDegree H I j)*(localDegree H I 2 u-meanDegree H I 2)+
        (1+meanDegree H I 2)*(localDegree H I j u-meanDegree H I j)-
        (duplicateExcess H I u:ℝ)*(localDegree H I j u-meanDegree H I j) := by
    have hd : localDegree H I 2 u = (closes H I u).card+(duplicateExcess H I u:ℝ) := by
      exact_mod_cast incident_card_eq_closes_add_excess hu
    rw [hd]
    ring
  rw [sum_congr rfl he, sum_sub_distrib, sum_add_distrib, ← mul_sum]
  change _ + (1+meanDegree H I 2)*
    (∑ u ∈ available H I, (localDegree H I j u-mean (available H I) (localDegree H I j))) - _ = _
  rw [centered_sum, mul_zero, add_zero]
  rfl

/-- The next available cardinality, not the old one, multiplies each mean
increment in the exact finite balance. Empty next states are included. -/
theorem weighted_mean_drift (H : Finset (Finset α)) (I : Finset α) (j : ℕ) :
    (∑ v ∈ available H I, (available H (insert v I)).card*
      (meanDegree H (insert v I) j-meanDegree H I j)) =
      (∑ u ∈ available H I, survivalDrift H I j u)-covariance H I j 2+
      (∑ u ∈ available H I, (duplicateExcess H I u:ℝ)*
        (localDegree H I j u-meanDegree H I j)) := by
  have hb := weighted_survivor_drift (available H I) (fun v => available H (insert v I))
    (fun v _ => available_antitone (subset_insert v I))
    (localDegree H I j) (fun v => localDegree H (insert v I) j)
  change _ = (∑ u ∈ available H I, survivalDrift H I j u)-
    (∑ u ∈ available H I, (((available H I).card:ℝ)-(safeChoices H I u).card)*
      (localDegree H I j u-meanDegree H I j)) at hb
  have he (u : α) (hu : u ∈ available H I) :
      ((available H I).card:ℝ)-(safeChoices H I u).card = 1+(closes H I u).card := by
    have hh := available_card_step hu
    rw [← safeChoices_eq_available hu] at hh
    have hh' : ((safeChoices H I u).card:ℝ)+1+(closes H I u).card = (available H I).card := by
      exact_mod_cast hh
    linarith only [hh']
  rw [sum_congr rfl (fun u hu => congrArg
    (fun b => b*(localDegree H I j u-meanDegree H I j)) (he u hu)), death_covariance] at hb
  change (∑ v ∈ available H I, (available H (insert v I)).card*
    (meanDegree H (insert v I) j-meanDegree H I j)) = _ at hb
  linarith only [hb]

/-- There are TWO negative variance contributions in the weighted drift of
the actual mean two-degree: neighbor loss and death bias. -/
theorem weighted_two_mean (H : Finset (Finset α)) (I : Finset α) :
    (∑ v ∈ available H I, (available H (insert v I)).card*
      (meanDegree H (insert v I) 2-meanDegree H I 2)) =
      (available H I).card*(2*meanDegree H I 3-(meanDegree H I 2)^2)-
      2*covariance H I 2 2+
      (∑ u ∈ available H I, GreedyTwoDegreeEnergy.correction H I u)+
      (∑ u ∈ available H I, (duplicateExcess H I u:ℝ)*
        (localDegree H I 2 u-meanDegree H I 2)) := by
  rw [weighted_mean_drift]
  have hm := GreedyTwoDegreeEnergy.mean_drift H I (meanDegree H I 2)
    (meanDegree_card H I 2).symm
  rw [← meanDegree_card H I 3, ← covariance_self] at hm
  rw [hm]
  ring

/-- Higher actual means have coefficient j, rather than j-1, on their
mixed covariance. Its sign is deliberately not asserted. -/
theorem weighted_higher_mean (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (hj : 1 ≤ j) :
    (∑ v ∈ available H I, (available H (insert v I)).card*
      (meanDegree H (insert v I) j-meanDegree H I j)) =
      (available H I).card*((j:ℝ)*meanDegree H I (j+1)-
        (j-1:ℕ)*meanDegree H I j*meanDegree H I 2)-
      (j:ℝ)*covariance H I j 2+
      (∑ u ∈ available H I, GreedyHigherDegreeEnergy.correction H I j u)+
      (∑ u ∈ available H I, (duplicateExcess H I u:ℝ)*
        (localDegree H I j u-meanDegree H I j)) := by
  rw [weighted_mean_drift]
  have hm := GreedyHigherDegreeEnergy.mean_drift H I j (meanDegree H I 2) (meanDegree H I j)
    (meanDegree_card H I 2).symm (meanDegree_card H I j).symm
  rw [← meanDegree_card H I (j+1)] at hm
  change _ = _-_-(j-1:ℕ)*covariance H I j 2+_ at hm
  rw [hm]
  have hc : ((j-1:ℕ):ℝ) = (j:ℝ)-1 := by rw [Nat.cast_sub hj, Nat.cast_one]
  rw [hc]
  ring

/-- Ordinary uniform conditional drift, with both negative variance and the
explicit current/next-cardinality reweighting cost retained. -/
theorem uniform_two_mean_upper (H : Finset (Finset α)) (I : Finset α)
    (hne : (available H I).Nonempty) (B E V : ℝ) (hB : 0 ≤ B)
    (hdeath : ∀ v ∈ available H I, 1+((closes H I v).card:ℝ) ≤ B)
    (hcorr : (∑ u ∈ available H I, GreedyTwoDegreeEnergy.correction H I u)+
      (∑ u ∈ available H I, (duplicateExcess H I u:ℝ)*
        (localDegree H I 2 u-meanDegree H I 2)) ≤ E)
    (hvariation : (∑ v ∈ available H I, |meanDegree H (insert v I) 2-meanDegree H I 2|) ≤ V) :
    (∑ v ∈ available H I, (meanDegree H (insert v I) 2-meanDegree H I 2))/(available H I).card ≤
      ((available H I).card*(2*meanDegree H I 3-(meanDegree H I 2)^2)-
        2*covariance H I 2 2+E+B*V)/((available H I).card:ℝ)^2 := by
  apply average_upper_of_weighted (available H I)
    (fun v => meanDegree H (insert v I) 2-meanDegree H I 2)
    (fun v => (available H (insert v I)).card) (available H I).card B _ V
    (by exact_mod_cast card_pos.mpr hne) hB _ _ hvariation
  · intro v hv
    have hd : ((available H (insert v I)).card:ℝ)+1+(closes H I v).card = (available H I).card := by
      exact_mod_cast available_card_step hv
    have he : ((available H I).card:ℝ)-(available H (insert v I)).card =
        1+(closes H I v).card := by linarith only [hd]
    rw [he, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1+(closes H I v).card)]
    exact hdeath v hv
  · rw [weighted_two_mean]
    linarith only [hcorr]

#print axioms death_covariance
#print axioms weighted_mean_drift
#print axioms weighted_two_mean
#print axioms weighted_higher_mean
#print axioms uniform_two_mean_upper
end
end Erdos773.GreedyAvailableMeanDrift
