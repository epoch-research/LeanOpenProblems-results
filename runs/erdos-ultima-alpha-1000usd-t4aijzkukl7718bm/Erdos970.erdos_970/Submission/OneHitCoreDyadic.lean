import Submission.PopulationTranslation

/-! Adjacent interval estimates with the exact core completion-weight second
moment retained. Tail moduli must be at least the doubled interval length.
No uniform relative-variance estimate is asserted. -/
namespace Erdos970.OneHitLogConcavity
open Finset GapAverages CoverFibers Resampling

lemma range_split_translate (m n : ℕ) :
    range (m+n) = range m ∪ (range n).image (fun x => m+x) := by
  ext x
  simp only [mem_range,mem_union,mem_image]
  constructor
  · intro hx
    by_cases hxm : x < m
    · exact Or.inl hxm
    · exact Or.inr ⟨x-m,by omega,by omega⟩
  · rintro (hx | ⟨y,hy,rfl⟩) <;> omega

lemma range_disjoint_translate (m n : ℕ) :
    Disjoint (range m) ((range n).image (fun x => m+x)) := by
  apply disjoint_left.mpr
  intro x hx hy
  obtain ⟨y,hy,rfl⟩ := mem_image.mp hy
  have := mem_range.mp hx
  omega

lemma range_translate_subset (m n : ℕ) :
    (range n).image (fun x => m+x) ⊆ range (m+n) := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
  exact mem_range.mpr (Nat.add_lt_add_left (mem_range.mp hy) m)

/-- The covariance of the two conditional core weights remains explicit. -/
theorem void_add_le_core_correlation (P R : Finset ℕ) (m n : ℕ)
    (hPR : Disjoint P R) (hR : ∀ p ∈ R, 0 < p ∧ m+n ≤ p) :
    coveredFraction (P ∪ R) (m+n) ≤ phaseMean P (fun r =>
      coreCoverWeight P R (range m) r *
        coreCoverWeight P R ((range n).image (fun x => m+x)) r) := by
  rw [void_eq_population,range_split_translate]
  exact population_cover_le_core_correlation P R _ _ (m+n) hPR hR
    (range_mono (by omega)) (range_translate_subset m n) (range_disjoint_translate m n)

/-- A rigorous but potentially enormous loss: the complete core phase count. -/
theorem void_add_le_core_phase_mass (P R : Finset ℕ) (m n : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hRprime : ∀ p ∈ R, p.Prime)
    (hPR : Disjoint P R) (hR : ∀ p ∈ R, 0 < p ∧ m+n ≤ p) :
    coveredFraction (P ∪ R) (m+n) ≤ (∏ p ∈ P, (p : ℝ))*
      coveredFraction (P ∪ R) m*coveredFraction (P ∪ R) n := by
  have hU : ∀ p ∈ P ∪ R, p.Prime := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · exact hP p hp
    · exact hRprime p hp
  have hh := population_cover_le_core_phase_mass P R (range m)
    ((range n).image (fun x => m+x)) (m+n) hP hPR hR
    (range_mono (by omega)) (range_translate_subset m n) (range_disjoint_translate m n)
  rw [← range_split_translate,populationCoveredFraction_image_add _ _ hU m,
    ← void_eq_population,← void_eq_population,← void_eq_population] at hh
  exact hh

/-- A one-hit tail reduces the dyadic problem to a scalar second moment of the
core completion weights. No independence between core translates is assumed. -/
theorem void_double_le_core_second_moment (P R : Finset ℕ) (m : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hRprime : ∀ p ∈ R, p.Prime)
    (hPR : Disjoint P R) (hR : ∀ p ∈ R, 0 < p ∧ 2*m ≤ p) :
    coveredFraction (P ∪ R) (2*m) ≤
      phaseMean P (fun r => coreCoverWeight P R (range m) r^2) := by
  have hh := population_cover_le_core_square_mean P R (range m)
    ((range m).image (fun x => m+x)) (m+m) hPR
    (fun p hp => ⟨(hR p hp).1,by have := (hR p hp).2; omega⟩)
    (range_mono (by omega)) (range_translate_subset m m) (range_disjoint_translate m m)
  rw [← range_split_translate,coreCoverWeight_distribution_image_add P R _ hP hRprime m
    (fun x => x^2),← void_eq_population] at hh
  simpa only [← two_mul m,add_self_div_two] using hh

noncomputable def coreWeightVariance (P R : Finset ℕ) (m : ℕ) : ℝ :=
  phaseMean P (fun r => (coreCoverWeight P R (range m) r-coveredFraction (P ∪ R) m)^2)

lemma coreWeightVariance_nonneg (P R : Finset ℕ) (m : ℕ) : 0 ≤ coreWeightVariance P R m := by
  unfold coreWeightVariance phaseMean
  exact div_nonneg (sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)

lemma core_weight_second_moment (P R : Finset ℕ) (m : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hPR : Disjoint P R) :
    phaseMean P (fun r => coreCoverWeight P R (range m) r^2) =
      coveredFraction (P ∪ R) m^2+coreWeightVariance P R m := by
  have he (r : Phase P) :
      (coreCoverWeight P R (range m) r-coveredFraction (P ∪ R) m)^2 =
      coreCoverWeight P R (range m) r^2-
        (2*coveredFraction (P ∪ R) m)*coreCoverWeight P R (range m) r+
          coveredFraction (P ∪ R) m^2 := by ring
  unfold coreWeightVariance
  simp_rw [he]
  rw [phaseMean_add,phaseMean_sub,phaseMean_mul,phaseMean_const P hP,
    coreCoverWeight_mean P R _ hPR,← void_eq_population]
  ring

/-- Relative core-weight variance is a sufficient hypothesis for a dyadic
loss. It has not been bounded uniformly by the number of selected primes. -/
theorem void_double_le_of_core_relative_variance (P R : Finset ℕ) (m : ℕ) (A : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hRprime : ∀ p ∈ R, p.Prime)
    (hPR : Disjoint P R) (hR : ∀ p ∈ R, 0 < p ∧ 2*m ≤ p)
    (hv : coreWeightVariance P R m ≤ (A-1)*coveredFraction (P ∪ R) m^2) :
    coveredFraction (P ∪ R) (2*m) ≤ A*coveredFraction (P ∪ R) m^2 := by
  have hh := void_double_le_core_second_moment P R m hP hRprime hPR hR
  rw [core_weight_second_moment P R m hP hPR] at hh
  nlinarith only [hh,hv]

#print axioms void_add_le_core_correlation
#print axioms void_add_le_core_phase_mass
#print axioms void_double_le_core_second_moment
#print axioms void_double_le_of_core_relative_variance
end Erdos970.OneHitLogConcavity
