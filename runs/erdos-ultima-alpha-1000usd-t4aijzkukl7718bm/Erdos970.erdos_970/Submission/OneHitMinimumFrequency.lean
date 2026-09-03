import Submission.OneHitCoreDyadic

/-! The frequency of minimum core counts gives a sharper one-hit-tail dyadic
loss than the complete core phase count. No uniform lower bound on this
frequency is asserted. -/
namespace Erdos970.OneHitLogConcavity
open Finset GapAverages CoverFibers Resampling

noncomputable def coreCountFrequency (P : Finset ℕ) (m s : ℕ) : ℝ :=
  phaseMean P (fun r => if (populationSurvivors (range m) P r).card = s then 1 else 0)

lemma coreCountFrequency_nonneg (P : Finset ℕ) (m s : ℕ) :
    0 ≤ coreCountFrequency P m s := by
  unfold coreCountFrequency phaseMean
  exact div_nonneg (sum_nonneg (fun _ _ => by split_ifs <;> norm_num)) (by positivity)

lemma phaseMean_nonneg_of (P : Finset ℕ) (f : Phase P → ℝ) (hf : ∀ r, 0 ≤ f r) :
    0 ≤ phaseMean P f := by
  unfold phaseMean
  exact div_nonneg (sum_nonneg (fun r _ => hf r)) (by positivity)

/-- A maximum atom controls the relative second moment of a nonnegative
weight. The atom's probability is retained explicitly, including the zero case. -/
lemma maximum_frequency_second_moment (P : Finset ℕ)
    (f : Phase P → ℝ) (C : ℝ) (A : Phase P → Prop) [DecidablePred A]
    (hf : ∀ r, 0 ≤ f r) (hC : ∀ r, f r ≤ C) (hA : ∀ r, A r → f r = C) :
    phaseMean P (fun r => if A r then (1 : ℝ) else 0) *
      phaseMean P (fun r => f r^2) ≤ phaseMean P f^2 := by
  let a := phaseMean P (fun r => if A r then (1 : ℝ) else 0)
  have ha : 0 ≤ a := phaseMean_nonneg_of P _ (fun r => by split_ifs <;> norm_num)
  have hm : 0 ≤ phaseMean P f := phaseMean_nonneg_of P f hf
  have hlow : a*C ≤ phaseMean P f := by
    have hh := phaseMean_mono P (fun r =>
      show C*(if A r then (1 : ℝ) else 0) ≤ f r by
        split_ifs with hr
        · rw [hA r hr,mul_one]
        · simpa only [mul_zero] using hf r)
    rw [phaseMean_mul] at hh
    simpa only [mul_comm] using hh
  have hsq : phaseMean P (fun r => f r^2) ≤ C*phaseMean P f := by
    have hh := phaseMean_mono P (fun r =>
      show f r^2 ≤ C*f r by
        have := mul_le_mul_of_nonneg_right (hC r) (hf r)
        nlinarith only [this])
    rwa [phaseMean_mul] at hh
  have hmul := mul_le_mul_of_nonneg_left hsq ha
  have hmul' := mul_le_mul_of_nonneg_right hlow hm
  change a*phaseMean P (fun r => f r^2) ≤ _
  nlinarith only [hmul,hmul']

/-- Minimum core counts maximize completion probability in the one-hit regime.
This uses the exact occupancy model, not independent thinning of positions. -/
lemma coreCoverWeight_le_minimum (P R : Finset ℕ) (m s : ℕ)
    (hR : ∀ p ∈ R, 0 < p ∧ m ≤ p)
    (hmin : ∀ r : Phase P, s ≤ (populationSurvivors (range m) P r).card) (r : Phase P) :
    coreCoverWeight P R (range m) r ≤ occupancy R.toList s := by
  unfold coreCoverWeight
  have hS : populationSurvivors (range m) P r ⊆ range m := filter_subset _ _
  rw [population_eq_finset_occupancy R _ m hR hS]
  apply (occupancy_shape R.toList m (fun p hp => hR p (by simpa using hp))).antitone
    (hmin r)
  exact (card_le_card hS).trans_eq (card_range m)

/-- The inverse minimum-count frequency is a valid dyadic loss for a one-hit
 tail. Its possible size is not bounded by a power of the prime budget here. -/
theorem minimum_frequency_mul_void_double_le (P R : Finset ℕ) (m s : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hRprime : ∀ p ∈ R, p.Prime)
    (hPR : Disjoint P R) (hR : ∀ p ∈ R, 0 < p ∧ 2*m ≤ p)
    (hmin : ∀ r : Phase P, s ≤ (populationSurvivors (range m) P r).card) :
    coreCountFrequency P m s * coveredFraction (P ∪ R) (2*m) ≤
      coveredFraction (P ∪ R) m^2 := by
  have hR' : ∀ p ∈ R, 0 < p ∧ m ≤ p :=
    fun p hp => ⟨(hR p hp).1,by have := (hR p hp).2; omega⟩
  have hh := maximum_frequency_second_moment P (coreCoverWeight P R (range m))
    (occupancy R.toList s) (fun r => (populationSurvivors (range m) P r).card = s)
    (coreCoverWeight_nonneg P R _) (coreCoverWeight_le_minimum P R m s hR' hmin)
    (fun r hr => by
      unfold coreCoverWeight
      have hS : populationSurvivors (range m) P r ⊆ range m := filter_subset _ _
      rw [population_eq_finset_occupancy R _ m hR' hS,hr])
  rw [coreCoverWeight_mean P R _ hPR,← void_eq_population] at hh
  exact (mul_le_mul_of_nonneg_left
    (void_double_le_core_second_moment P R m hP hRprime hPR hR)
    (coreCountFrequency_nonneg P m s)).trans hh

/-- An explicitly supplied minimum-frequency lower bound gives the corresponding
finite dyadic constant. This does not prove such a bound for arbitrary cores. -/
theorem void_double_le_of_minimum_frequency (P R : Finset ℕ) (m s : ℕ) (b : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hRprime : ∀ p ∈ R, p.Prime)
    (hPR : Disjoint P R) (hR : ∀ p ∈ R, 0 < p ∧ 2*m ≤ p)
    (hmin : ∀ r : Phase P, s ≤ (populationSurvivors (range m) P r).card)
    (hb : 0 < b) (hfreq : b ≤ coreCountFrequency P m s) :
    coveredFraction (P ∪ R) (2*m) ≤ coveredFraction (P ∪ R) m^2/b := by
  apply (le_div_iff₀ hb).mpr
  have hv0 : 0 ≤ coveredFraction (P ∪ R) (2*m) := by
    rw [void_eq_population]
    exact populationCoveredFraction_nonneg _ _
  have hm := mul_le_mul_of_nonneg_right hfreq hv0
  have hh := minimum_frequency_mul_void_double_le P R m s hP hRprime hPR hR hmin
  nlinarith only [hm,hh]

#print axioms maximum_frequency_second_moment
#print axioms coreCoverWeight_le_minimum
#print axioms minimum_frequency_mul_void_double_le
#print axioms void_double_le_of_minimum_frequency
end Erdos970.OneHitLogConcavity
