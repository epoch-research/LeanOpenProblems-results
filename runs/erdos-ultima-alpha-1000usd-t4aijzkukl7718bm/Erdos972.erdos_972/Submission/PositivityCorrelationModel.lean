import FormalConjecturesUtil

/-!
A finite diagnostic model for the positivity route. This is NOT a model of
prime numbers or of the floor map, and is NOT a disproof of Erdős 972.

The two profile variables are independent, and each source has conditional
mean one against every function of the opposite profile. The sources are
nonnegative, have mean one, and equal their profiles wherever positive.
Nevertheless their product vanishes identically. Even a strictly positive
joint majorant-residual product does not give a strict correlation gap.
-/
namespace Erdos972PositivityCorrelationModel

open Finset

noncomputable def average (v : Fin 12 → ℝ) : ℝ := (∑ i, v i) / 12

noncomputable def covariance (v w : Fin 12 → ℝ) : ℝ :=
  average (fun i => v i * w i) - average v * average w

noncomputable def source₁ : Fin 12 → ℝ := ![6, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0]
noncomputable def source₂ : Fin 12 → ℝ := ![0, 6, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0]
noncomputable def profile₁ : Fin 12 → ℝ := ![6, 6, 6, 6, 6, 6, -4, -4, -4, -4, -4, -4]
noncomputable def profile₂ : Fin 12 → ℝ := ![6, 6, 6, -4, -4, -4, 6, 6, 6, -4, -4, -4]

noncomputable def remainder₁ (i : Fin 12) : ℝ := source₁ i - profile₁ i
noncomputable def remainder₂ (i : Fin 12) : ℝ := source₂ i - profile₂ i
noncomputable def majorant₁ (i : Fin 12) : ℝ := max (profile₁ i) 0
noncomputable def majorant₂ (i : Fin 12) : ℝ := max (profile₂ i) 0

lemma source_bounds (i : Fin 12) :
    0 ≤ source₁ i ∧ 0 ≤ source₂ i ∧ source₁ i ≤ majorant₁ i ∧
      source₂ i ≤ majorant₂ i := by
  fin_cases i <;>
    norm_num [source₁, source₂, majorant₁, majorant₂, profile₁, profile₂]

lemma profile_eq_on_positive_source (i : Fin 12) :
    (0 < source₁ i → profile₁ i = source₁ i) ∧
      (0 < source₂ i → profile₂ i = source₂ i) := by
  fin_cases i <;> norm_num [source₁, source₂, profile₁, profile₂]

lemma source_product_zero (i : Fin 12) : source₁ i * source₂ i = 0 := by
  fin_cases i <;> norm_num [source₁, source₂]

lemma means : average source₁ = 1 ∧ average source₂ = 1 ∧
    average profile₁ = 1 ∧ average profile₂ = 1 := by
  norm_num [average, Fin.sum_univ_succ, source₁, source₂, profile₁, profile₂]

/-- Full independence of the two finite profiles, including nonlinear functions. -/
lemma profile_independence (Φ Ψ : ℝ → ℝ) :
    average (fun i => Φ (profile₁ i) * Ψ (profile₂ i)) =
      average (fun i => Φ (profile₁ i)) * average (fun i => Ψ (profile₂ i)) := by
  simp [average, Fin.sum_univ_succ, profile₁, profile₂]
  ring

/-- Every function of the first profile has the predicted second-source mean. -/
lemma first_profile_second_source (Φ : ℝ → ℝ) :
    average (fun i => Φ (profile₁ i) * source₂ i) =
      average (fun i => Φ (profile₁ i)) := by
  simp [average, Fin.sum_univ_succ, profile₁, source₂]
  ring

/-- Every function of the second profile has the predicted first-source mean. -/
lemma first_source_second_profile (Ψ : ℝ → ℝ) :
    average (fun i => source₁ i * Ψ (profile₂ i)) =
      average (fun i => Ψ (profile₂ i)) := by
  simp [average, Fin.sum_univ_succ, source₁, profile₂]
  ring

lemma three_covariances_zero :
    covariance profile₁ source₂ = 0 ∧ covariance source₁ profile₂ = 0 ∧
      covariance profile₁ profile₂ = 0 := by
  norm_num [covariance, average, Fin.sum_univ_succ,
    source₁, source₂, profile₁, profile₂]

lemma nonlinear_covariances_zero :
    covariance (fun i => max (remainder₁ i) 0) source₂ = 0 ∧
    covariance source₁ (fun i => max (remainder₂ i) 0) = 0 ∧
    covariance (fun i => max (remainder₁ i) 0)
      (fun i => max (remainder₂ i) 0) = 0 := by
  norm_num [covariance, average, Fin.sum_univ_succ, remainder₁, remainder₂,
    source₁, source₂, profile₁, profile₂]

lemma majorant_means : average majorant₁ = 3 ∧ average majorant₂ = 3 := by
  norm_num [average, Fin.sum_univ_succ, majorant₁, majorant₂, profile₁, profile₂]

/-- Simultaneous nonzero composite residuals have strictly positive mean. -/
lemma residual_product_mean :
    average (fun i => (majorant₁ i - source₁ i) * (majorant₂ i - source₂ i)) = 3 := by
  norm_num [average, Fin.sum_univ_succ, majorant₁, majorant₂,
    source₁, source₂, profile₁, profile₂]

lemma negative_centered_remainder : covariance remainder₁ remainder₂ = -1 := by
  norm_num [covariance, average, Fin.sum_univ_succ, remainder₁, remainder₂,
    source₁, source₂, profile₁, profile₂]

/-- These finite mean, profile-independence and mixed-profile identities alone
cannot imply a positive simultaneous-source mean. This says nothing about
whether the additional arithmetic of actual primes supplies that conclusion. -/
theorem finite_positivity_obstruction :
    ∃ f g A B : Fin 12 → ℝ,
      (∀ i, 0 ≤ f i ∧ 0 ≤ g i ∧ f i ≤ max (A i) 0 ∧ g i ≤ max (B i) 0) ∧
      average f = 1 ∧ average g = 1 ∧ average A = 1 ∧ average B = 1 ∧
      (∀ Φ Ψ : ℝ → ℝ, average (fun i => Φ (A i) * Ψ (B i)) =
        average (fun i => Φ (A i)) * average (fun i => Ψ (B i))) ∧
      (∀ Φ : ℝ → ℝ, average (fun i => Φ (A i) * g i) =
        average (fun i => Φ (A i))) ∧
      (∀ Ψ : ℝ → ℝ, average (fun i => f i * Ψ (B i)) =
        average (fun i => Ψ (B i))) ∧
      average (fun i => max (A i) 0) = 3 ∧ average (fun i => max (B i) 0) = 3 ∧
      average (fun i => (max (A i) 0 - f i) * (max (B i) 0 - g i)) = 3 ∧
      (∀ i, f i * g i = 0) ∧
      covariance (fun i => f i - A i) (fun i => g i - B i) = -1 := by
  exact ⟨source₁, source₂, profile₁, profile₂, source_bounds,
    means.1, means.2.1, means.2.2.1, means.2.2.2,
    profile_independence, first_profile_second_source, first_source_second_profile,
    majorant_means.1, majorant_means.2, residual_product_mean,
    source_product_zero, negative_centered_remainder⟩

#print axioms finite_positivity_obstruction
#print axioms nonlinear_covariances_zero
#print axioms profile_eq_on_positive_source

end Erdos972PositivityCorrelationModel
