import Submission.GreedyCodegreeProfileDrift

/-!
The exact distinction between summed survival-conditioned local drift and
the drift of total degrees on the changing available set. Vertex deaths
must be charged, even if auxiliary records freeze at their old values.
-/
namespace Erdos773.GreedySurvivalTotalDrift
open Finset GreedyHypergraphState GreedyLinearLocal GreedyProfileDrift
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- Double-count the surviving pairs of a finite transition relation. -/
lemma survivor_sum (S : Finset α) (T : α → Finset α) (hT : ∀ v ∈ S, T v ⊆ S)
    (f : α → α → ℝ) :
    (∑ v ∈ S, ∑ u ∈ T v, f v u) =
      ∑ u ∈ S, ∑ v ∈ S.filter (fun v => u ∈ T v), f v u := by
  classical
  have he (v : α) (hv : v ∈ S) : (∑ u ∈ T v, f v u) =
      ∑ u ∈ S, if u ∈ T v then f v u else 0 := by
    rw [← sum_filter]
    congr 1
    ext u
    simp only [mem_filter]
    exact ⟨fun hu => ⟨hT v hv hu,hu⟩,fun hu => hu.2⟩
  rw [sum_congr rfl he,sum_comm]
  apply sum_congr rfl
  intro u hu
  rw [sum_filter]

omit [Fintype α] in
/-- Sum of actual increments equals sum of surviving increments minus the
old mass at every killed vertex. This is purely finite bookkeeping. -/
lemma survival_balance (S : Finset α) (T : α → Finset α) (hT : ∀ v ∈ S, T v ⊆ S)
    (D : α → ℝ) (F : α → α → ℝ) :
    (∑ v ∈ S, ((∑ u ∈ T v, F v u)-(∑ u ∈ S, D u))) =
      (∑ u ∈ S, ∑ v ∈ S.filter (fun v => u ∈ T v), (F v u-D u))-
      (∑ u ∈ S, ((S.card:ℝ)-(S.filter (fun v => u ∈ T v)).card)*D u) := by
  rw [sum_sub_distrib,survivor_sum S T hT,sum_const,nsmul_eq_mul]
  simp_rw [sum_sub_distrib,sum_const,nsmul_eq_mul,sub_mul]
  rw [sum_sub_distrib,mul_sum]
  ring

abbrev totalDegree (H : Finset (Finset α)) (I : Finset α) (j : ℕ) : ℝ :=
  ∑ u ∈ available H I, ((incident H I j u).card:ℝ)

/-- Actual total-degree drift, including the death term. No linearity or
uniform degree hypothesis is used. -/
theorem total_drift (H : Finset (Finset α)) (I : Finset α) (j : ℕ) :
    (∑ v ∈ available H I, (totalDegree H (insert v I) j-totalDegree H I j)) =
      (∑ u ∈ available H I, survivalDrift H I j u)-
      (∑ u ∈ available H I, (1+((closes H I u).card:ℝ))*(incident H I j u).card) := by
  have hb := survival_balance (available H I) (fun v => available H (insert v I))
    (fun v _ => available_antitone (subset_insert v I))
    (fun u => ((incident H I j u).card:ℝ))
    (fun v u => ((incident H (insert v I) j u).card:ℝ))
  change _ = (∑ u ∈ available H I, survivalDrift H I j u)-
    (∑ u ∈ available H I, (((available H I).card:ℝ)-(safeChoices H I u).card)*
      (incident H I j u).card) at hb
  rw [hb]
  congr 1
  apply sum_congr rfl
  intro u hu
  have hs := available_card_step hu
  rw [← safeChoices_eq_available hu] at hs
  have hsR : ((safeChoices H I u).card:ℝ)+1+(closes H I u).card = (available H I).card := by
    exact_mod_cast hs
  congr 1
  linarith only [hsR]

/-- In multiplicity-counted coordinates, duplicates correct the death cost
rather than silently changing the survival drift. -/
theorem total_drift_with_excess (H : Finset (Finset α)) (I : Finset α) (j : ℕ) :
    (∑ v ∈ available H I, (totalDegree H (insert v I) j-totalDegree H I j)) =
      (∑ u ∈ available H I, survivalDrift H I j u)-totalDegree H I j-
      (∑ u ∈ available H I, ((incident H I 2 u).card:ℝ)*(incident H I j u).card)+
      (∑ u ∈ available H I, (duplicateExcess H I u:ℝ)*(incident H I j u).card) := by
  rw [total_drift]
  have he (u : α) (hu : u ∈ available H I) :
      (1+((closes H I u).card:ℝ))*(incident H I j u).card =
        (incident H I j u).card+((incident H I 2 u).card:ℝ)*(incident H I j u).card-
          (duplicateExcess H I u:ℝ)*(incident H I j u).card := by
    have hd : ((incident H I 2 u).card:ℝ) = (closes H I u).card+(duplicateExcess H I u:ℝ) := by
      exact_mod_cast incident_card_eq_closes_add_excess hu
    rw [hd]
    ring
  rw [sum_congr rfl he,sum_sub_distrib,sum_add_distrib]
  dsimp only [totalDegree]
  ring

#print axioms survivor_sum
#print axioms survival_balance
#print axioms total_drift
#print axioms total_drift_with_excess
end
end Erdos773.GreedySurvivalTotalDrift
