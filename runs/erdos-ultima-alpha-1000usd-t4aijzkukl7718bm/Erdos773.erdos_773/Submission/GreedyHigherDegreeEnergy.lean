import Submission.GreedyHigherPairWeights

/-!
Higher-degree drift in symmetric pair-weight form. Its nonlinear correction
is bounded independently of the leading two-degree profile error. Summed
drift has an exact covariance correction. These are state identities, not
yet a stochastic estimate on the changing available-vertex averages.
-/
namespace Erdos773.GreedyHigherDegreeEnergy
open Finset GreedyHypergraphState GreedyCommonNeighbors GreedyLinearLocal
open GreedyCodegreeDrift GreedyCodegreeHigherDrift GreedyLinearHigherDrift
open GreedyHigherPairWeights
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def correction (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (u : α) : ℝ :=
  (∑ v ∈ available H I, weight H I j u v*(duplicateExcess H I v:ℝ))+
    (neighborWeight H I j u:ℝ)-
    (∑ w ∈ safeChoices H I u, ((localLost H I j u w).card:ℝ))-
    (promotionDefect H I j u:ℝ)

lemma neighborWeight_degree (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (u : α) :
    (neighborWeight H I j u:ℝ) =
      (∑ v ∈ available H I, weight H I j u v*(incident H I 2 v).card)-
      (∑ v ∈ available H I, weight H I j u v*(duplicateExcess H I v:ℝ)) := by
  rw [neighborWeight_eq,← sum_sub_distrib]
  apply sum_congr rfl
  intro v hv
  have hd : ((incident H I 2 v).card:ℝ) = (closes H I v).card+(duplicateExcess H I v:ℝ) := by
    exact_mod_cast incident_card_eq_closes_add_excess hv
  rw [hd]
  ring

/-- Exact higher-degree drift with the symmetric pair-weight operator. -/
theorem weighted_drift (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (u : α) :
    survivalDrift H I j u = (j:ℝ)*(incident H I (j+1) u).card-
      (∑ v ∈ available H I, weight H I j u v*(incident H I 2 v).card)+correction H I j u := by
  have hb := survival_drift_balance H I j u
  unfold correction
  rw [neighborWeight_degree]
  linarith only [hb]

/-- All omitted intersections, duplicate residual pairs, and failed
promotions are contained in this bounded correction. No leading term
proportional to the neighbor two-degree error is discarded. -/
theorem correction_bounds {H : Finset (Finset α)} (I : Finset α) (j : ℕ)
    (hj : 3 ≤ j) (u : α) (E P : ℝ) (C : ℕ)
    (hE : ∀ v ∈ available H I, (duplicateExcess H I v:ℝ) ≤ E)
    (hC : ∀ x ∈ available H I, ∀ y ∈ available H I, x ≠ y → commonDegree H I x y ≤ C)
    (hP : (promotionDefect H I j u:ℝ) ≤ P) :
    -(j-1:ℕ)*(incident H I j u).card-P ≤ correction H I j u ∧
    correction H I j u ≤ ((j-1:ℕ)*(E+1)+(j.choose 2:ℝ)*C)*(incident H I j u).card := by
  have hdup : (∑ v ∈ available H I, weight H I j u v*(duplicateExcess H I v:ℝ)) ≤
      (j-1:ℕ)*(incident H I j u).card*E := by
    calc
      _ ≤ ∑ v ∈ available H I, weight H I j u v*E :=
        sum_le_sum (fun v hv => mul_le_mul_of_nonneg_left (hE v hv) (by positivity))
      _ = _ := by rw [← sum_mul,weighted_degree]
  have hdup0 : (0:ℝ) ≤ ∑ v ∈ available H I, weight H I j u v*(duplicateExcess H I v:ℝ) := by positivity
  have hp0 : (0:ℝ) ≤ promotionDefect H I j u := by positivity
  obtain ⟨hl,hh⟩ := sum_localLost_bounds I j hj u C hC
  have hlR : (∑ w ∈ safeChoices H I u, ((localLost H I j u w).card:ℝ)) ≤
      (j-1:ℕ)*(incident H I j u).card+(neighborWeight H I j u:ℝ) := by exact_mod_cast hl
  have hhR : (neighborWeight H I j u:ℝ) ≤
      (∑ w ∈ safeChoices H I u, ((localLost H I j u w).card:ℝ))+
        ((j.choose 2:ℝ)*C+(j-1:ℕ))*(incident H I j u).card := by exact_mod_cast hh
  unfold correction
  constructor <;> nlinarith only [hdup,hdup0,hp0,hlR,hhR,hP]

/-- Centering preserves the weighted-neighbor error and the self damping. -/
theorem centered_drift (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (u : α) (f2 fj fn : ℝ) :
    survivalDrift H I j u-((j:ℝ)*fn-(j-1:ℕ)*f2*fj) =
      (j:ℝ)*((incident H I (j+1) u).card-fn)-
        (j-1:ℕ)*f2*((incident H I j u).card-fj)-
      (∑ v ∈ available H I, weight H I j u v*((incident H I 2 v).card-f2))+correction H I j u := by
  have hs : (∑ v ∈ available H I, weight H I j u v*((incident H I 2 v).card-f2)) =
      (∑ v ∈ available H I, weight H I j u v*(incident H I 2 v).card)-
        (j-1:ℕ)*(incident H I j u).card*f2 := by
    simp_rw [mul_sub]
    rw [sum_sub_distrib,← sum_mul,weighted_degree]
  rw [hs,weighted_drift]
  ring

/-- Exact covariance correction in the SUM of survival-conditioned drifts.
This sum is not silently identified with the drift of a moving average. -/
theorem mean_drift (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (f2 fj : ℝ)
    (h2 : (∑ u ∈ available H I, ((incident H I 2 u).card:ℝ)) = (available H I).card*f2)
    (hj : (∑ u ∈ available H I, ((incident H I j u).card:ℝ)) = (available H I).card*fj) :
    (∑ u ∈ available H I, survivalDrift H I j u) =
      (j:ℝ)*(∑ u ∈ available H I, ((incident H I (j+1) u).card:ℝ))-
      (j-1:ℕ)*(available H I).card*fj*f2-
      (j-1:ℕ)*(∑ u ∈ available H I,
        (((incident H I j u).card:ℝ)-fj)*(((incident H I 2 u).card:ℝ)-f2))+
      (∑ u ∈ available H I, correction H I j u) := by
  have hs := sum_congr (s₁ := available H I) rfl (fun u _ => weighted_drift H I j u)
  rw [sum_add_distrib,sum_sub_distrib,← mul_sum,sum_weighted] at hs
  have hcov : (∑ u ∈ available H I,
      (((incident H I j u).card:ℝ)-fj)*(((incident H I 2 u).card:ℝ)-f2)) =
      (∑ u ∈ available H I, ((incident H I j u).card:ℝ)*(incident H I 2 u).card)-
        (available H I).card*fj*f2 := by
    simp_rw [sub_mul,mul_sub]
    rw [sum_sub_distrib,sum_sub_distrib,sum_sub_distrib,← sum_mul,← mul_sum,hj,h2,sum_const,nsmul_eq_mul]
    ring
  rw [hs,hcov]
  ring

#print axioms neighborWeight_degree
#print axioms weighted_drift
#print axioms correction_bounds
#print axioms centered_drift
#print axioms mean_drift
end
end Erdos773.GreedyHigherDegreeEnergy
