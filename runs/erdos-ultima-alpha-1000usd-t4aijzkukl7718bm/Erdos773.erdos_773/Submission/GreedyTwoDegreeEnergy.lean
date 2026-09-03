import Submission.GreedyCodegreeTwoDrift
import Submission.GreedyWeightedDissipation

/-!
Exact two-degree energy and mean-drift identities. Residual-pair
multiplicities are symmetric weights. Their full self-plus-neighbor term
is dissipative, rather than an absolute-error cost of leading order.
These identities do not assert a concentration or extraction theorem.
-/
namespace Erdos773.GreedyTwoDegreeEnergy
open Finset GreedyHypergraphState GreedyCommonNeighbors GreedyLinearLocal
open GreedyCodegreeDrift GreedyCodegreeTwoDrift GreedyLinearHigherDrift
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev weight (H : Finset (Finset α)) (I : Finset α) (u v : α) : ℝ :=
  (pairReps H I u v).card

omit [Fintype α] in
lemma weight_symm (H : Finset (Finset α)) (I : Finset α) (u v : α) :
    weight H I u v = weight H I v u := by
  have he : pairReps H I u v = pairReps H I v u := by
    ext e
    simp only [pairReps,mem_filter,ne_comm,Finset.pair_comm]
  rw [weight,weight,he]

lemma sum_weight (H : Finset (Finset α)) (I : Finset α) (u : α) (f : α → ℝ) :
    (∑ v ∈ available H I, weight H I u v*f v) =
      ∑ v ∈ closes H I u, weight H I u v*f v := by
  symm
  apply sum_subset (closes_subset H I u)
  intro v hv hnc
  have he : pairReps H I u v = ∅ :=
    not_nonempty_iff_eq_empty.mp (fun h => hnc ((pairReps_nonempty_iff hv).mp h))
  simp [weight,he]

lemma weighted_degree {H : Finset (Finset α)} {I : Finset α} {u : α}
    (hu : u ∈ available H I) :
    (∑ v ∈ available H I, weight H I u v) = (incident H I 2 u).card := by
  have hh := sum_weight H I u (fun _ => 1)
  simp only [mul_one] at hh
  rw [hh]
  exact_mod_cast (incident_two_card hu).symm

/-- All nonlinear corrections to the weighted two-degree loss. -/
def correction (H : Finset (Finset α)) (I : Finset α) (u : α) : ℝ :=
  (∑ v ∈ available H I, weight H I u v*
    ((duplicateExcess H I v:ℝ)+1+(commonDegree H I u v:ℝ)))-
    (promotionDefect H I 2 u:ℝ)

/-- Exact local drift with a symmetric weighted-neighbor term. -/
theorem weighted_drift {H : Finset (Finset α)} {I : Finset α} {u : α}
    (hu : u ∈ available H I) :
    survivalDrift H I 2 u = 2*(incident H I 3 u).card-
      (∑ v ∈ available H I, weight H I u v*(incident H I 2 v).card)+correction H I u := by
  have hb := survival_drift_balance H I 2 u
  have hloss : (∑ w ∈ safeChoices H I u, ((localLost H I 2 u w).card:ℝ)) =
      ∑ v ∈ closes H I u, weight H I u v*(restrictedClosure H I u v).card := by
    exact_mod_cast sum_localLost_two I u
  have hc (v : α) (hv : v ∈ closes H I u) :
      ((restrictedClosure H I u v).card:ℝ) = (incident H I 2 v).card-
        ((duplicateExcess H I v:ℝ)+1+(commonDegree H I u v:ℝ)) := by
    have h₁ : ((restrictedClosure H I u v).card:ℝ)+1+(commonDegree H I u v:ℝ) =
        (closes H I v).card := by exact_mod_cast restrictedClosure_balance hu hv
    have h₂ : ((incident H I 2 v).card:ℝ) = (closes H I v).card+(duplicateExcess H I v:ℝ) := by
      exact_mod_cast incident_card_eq_closes_add_excess (closes_subset H I u hv)
    linarith only [h₁,h₂]
  have hloss' : (∑ w ∈ safeChoices H I u, ((localLost H I 2 u w).card:ℝ)) =
      (∑ v ∈ available H I, weight H I u v*(incident H I 2 v).card)-
      (∑ v ∈ available H I, weight H I u v*((duplicateExcess H I v:ℝ)+1+(commonDegree H I u v:ℝ))) := by
    rw [hloss,sum_weight,sum_weight,← sum_sub_distrib]
    apply sum_congr rfl
    intro v hv
    rw [hc v hv]
    ring
  rw [hloss'] at hb
  norm_num only [Nat.cast_ofNat] at hb
  unfold correction
  linarith only [hb]

/-- Expanding around any pair of scalar centers retains the actual weighted
neighbor errors; no absolute maximum is substituted for them. -/
theorem centered_drift {H : Finset (Finset α)} {I : Finset α} {u : α}
    (hu : u ∈ available H I) (f2 f3 : ℝ) :
    survivalDrift H I 2 u-(2*f3-f2^2) =
      2*((incident H I 3 u).card-f3)-f2*((incident H I 2 u).card-f2)-
      (∑ v ∈ available H I, weight H I u v*((incident H I 2 v).card-f2))+correction H I u := by
  have hs : (∑ v ∈ available H I, weight H I u v*((incident H I 2 v).card-f2)) =
      (∑ v ∈ available H I, weight H I u v*(incident H I 2 v).card)-
        (incident H I 2 u).card*f2 := by
    simp_rw [mul_sub]
    rw [sum_sub_distrib,← sum_mul,weighted_degree hu]
  rw [hs,weighted_drift hu]
  ring

/-- Summing the weighted-neighbor term gives the sum of degree squares. -/
lemma sum_weighted_neighbors (H : Finset (Finset α)) (I : Finset α) :
    (∑ u ∈ available H I, ∑ v ∈ available H I,
      weight H I u v*(incident H I 2 v).card) =
      ∑ u ∈ available H I, ((incident H I 2 u).card:ℝ)^2 := by
  rw [sum_comm]
  apply sum_congr rfl
  intro u hu
  simp_rw [weight_symm H I _ u]
  rw [← sum_mul,weighted_degree hu]
  ring

/-- The variance correction in the TOTAL two-degree drift has a favorable
negative sign. Here f2 is assumed to be the actual available-vertex mean. -/
theorem mean_drift (H : Finset (Finset α)) (I : Finset α) (f2 : ℝ)
    (hmean : (∑ u ∈ available H I, ((incident H I 2 u).card:ℝ)) =
      (available H I).card*f2) :
    (∑ u ∈ available H I, survivalDrift H I 2 u) =
      2*(∑ u ∈ available H I, ((incident H I 3 u).card:ℝ))-
      (available H I).card*f2^2-
      (∑ u ∈ available H I, (((incident H I 2 u).card:ℝ)-f2)^2)+
      (∑ u ∈ available H I, correction H I u) := by
  have hs := sum_congr (s₁ := available H I) rfl (fun u hu => weighted_drift hu)
  rw [sum_add_distrib,sum_sub_distrib,← mul_sum,sum_weighted_neighbors] at hs
  have hvar : (∑ u ∈ available H I, (((incident H I 2 u).card:ℝ)-f2)^2) =
      (∑ u ∈ available H I, ((incident H I 2 u).card:ℝ)^2)-(available H I).card*f2^2 := by
    simp_rw [sub_sq]
    rw [sum_add_distrib,sum_sub_distrib]
    simp_rw [mul_assoc]
    rw [← mul_sum,← sum_mul,hmean,sum_const,nsmul_eq_mul]
    ring
  rw [hs,hvar]
  ring

/-- Exact quadratic drift pairing. The leading neighbor interaction is a
negative sum of squares, with only cubic and explicit nonlinear errors left. -/
theorem energy_identity (H : Finset (Finset α)) (I : Finset α) (f2 f3 : ℝ) :
    (∑ u ∈ available H I, (((incident H I 2 u).card:ℝ)-f2)*
      (survivalDrift H I 2 u-(2*f3-f2^2))) =
    2*(∑ u ∈ available H I, (((incident H I 2 u).card:ℝ)-f2)*
      (((incident H I 3 u).card:ℝ)-f3))-
    (1/2:ℝ)*(∑ u ∈ available H I, ∑ v ∈ available H I, weight H I u v*
      ((((incident H I 2 u).card:ℝ)-f2)+(((incident H I 2 v).card:ℝ)-f2))^2)+
    (∑ u ∈ available H I, (((incident H I 2 u).card:ℝ)-f2)^3)+
    (∑ u ∈ available H I, (((incident H I 2 u).card:ℝ)-f2)*correction H I u) := by
  let e : α → ℝ := fun u => (incident H I 2 u).card-f2
  have hsym := GreedyWeightedDissipation.quadratic_identity (available H I) (weight H I) e
    (fun u _ v _ => weight_symm H I u v)
  have he (u : α) (hu : u ∈ available H I) :
      e u*(survivalDrift H I 2 u-(2*f3-f2^2)) =
        2*(e u*((incident H I 3 u).card-f3))-
        e u*((∑ v ∈ available H I, weight H I u v)*e u+
          ∑ v ∈ available H I, weight H I u v*e v)+(e u)^3+e u*correction H I u := by
    rw [centered_drift hu f2 f3,weighted_degree hu]
    dsimp only [e]
    ring
  have hsum := sum_congr (s₁ := available H I) rfl he
  rw [sum_add_distrib,sum_add_distrib,sum_sub_distrib,← mul_sum,hsym] at hsum
  exact hsum

/-- The same cancellation is valid for odd monotone tests, as needed by
higher-moment potentials. No estimate on the sign of neighboring errors is
assumed. -/
theorem test_identity (H : Finset (Finset α)) (I : Finset α) (f2 f3 : ℝ) (φ : ℝ → ℝ) :
    (∑ u ∈ available H I, φ (((incident H I 2 u).card:ℝ)-f2)*
      (survivalDrift H I 2 u-(2*f3-f2^2))) =
    2*(∑ u ∈ available H I, φ (((incident H I 2 u).card:ℝ)-f2)*
      (((incident H I 3 u).card:ℝ)-f3))-
    (∑ u ∈ available H I, φ (((incident H I 2 u).card:ℝ)-f2)*
      ((∑ v ∈ available H I, weight H I u v)*(((incident H I 2 u).card:ℝ)-f2)+
        ∑ v ∈ available H I, weight H I u v*(((incident H I 2 v).card:ℝ)-f2)))+
    (∑ u ∈ available H I, φ (((incident H I 2 u).card:ℝ)-f2)*
      (((incident H I 2 u).card:ℝ)-f2)^2)+
    (∑ u ∈ available H I, φ (((incident H I 2 u).card:ℝ)-f2)*correction H I u) := by
  have he (u : α) (hu : u ∈ available H I) :
      φ (((incident H I 2 u).card:ℝ)-f2)*(survivalDrift H I 2 u-(2*f3-f2^2)) =
        2*(φ (((incident H I 2 u).card:ℝ)-f2)*(((incident H I 3 u).card:ℝ)-f3))-
        φ (((incident H I 2 u).card:ℝ)-f2)*
          ((∑ v ∈ available H I, weight H I u v)*(((incident H I 2 u).card:ℝ)-f2)+
            ∑ v ∈ available H I, weight H I u v*(((incident H I 2 v).card:ℝ)-f2))+
        φ (((incident H I 2 u).card:ℝ)-f2)*(((incident H I 2 u).card:ℝ)-f2)^2+
        φ (((incident H I 2 u).card:ℝ)-f2)*correction H I u := by
    rw [centered_drift hu f2 f3,weighted_degree hu]
    ring
  rw [sum_congr rfl he,sum_add_distrib,sum_add_distrib,sum_sub_distrib,← mul_sum]

/-- After summing against an odd monotone test, the entire leading
self-plus-neighbor interaction may be dropped with the FAVORABLE sign. -/
theorem test_drift_bound (H : Finset (Finset α)) (I : Finset α) (f2 f3 : ℝ)
    (φ : ℝ → ℝ) (hmono : Monotone φ) (hodd : ∀ x, φ (-x) = -φ x) :
    (∑ u ∈ available H I, φ (((incident H I 2 u).card:ℝ)-f2)*
      (survivalDrift H I 2 u-(2*f3-f2^2))) ≤
    2*(∑ u ∈ available H I, φ (((incident H I 2 u).card:ℝ)-f2)*
      (((incident H I 3 u).card:ℝ)-f3))+
    (∑ u ∈ available H I, φ (((incident H I 2 u).card:ℝ)-f2)*
      (((incident H I 2 u).card:ℝ)-f2)^2)+
    (∑ u ∈ available H I, φ (((incident H I 2 u).card:ℝ)-f2)*correction H I u) := by
  have hn := GreedyWeightedDissipation.nonnegative (available H I) (weight H I)
    (fun u => ((incident H I 2 u).card:ℝ)-f2) φ
    (fun u _ v _ => weight_symm H I u v) (fun _ _ _ _ => by positivity) hmono hodd
  rw [test_identity]
  linarith only [hn]

#print axioms weight_symm
#print axioms sum_weight
#print axioms weighted_degree
#print axioms weighted_drift
#print axioms centered_drift
#print axioms sum_weighted_neighbors
#print axioms mean_drift
#print axioms energy_identity
#print axioms test_identity
#print axioms test_drift_bound
end
end Erdos773.GreedyTwoDegreeEnergy
