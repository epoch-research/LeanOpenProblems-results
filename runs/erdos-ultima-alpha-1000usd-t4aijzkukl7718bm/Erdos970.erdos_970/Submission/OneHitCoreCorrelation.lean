import Submission.OneHitPopulationDoubling

/-! Conditional negative dependence for disjoint populations under a common
core phase. The core correlation is not discarded. An elementary finite-phase
bound is also supplied, but its loss can be exponentially large in the budget. -/
namespace Erdos970.OneHitLogConcavity
open Finset GapAverages CoverFibers Resampling

lemma populationCoveredFraction_nonneg (S P : Finset ℕ) :
    0 ≤ populationCoveredFraction S P := by
  unfold populationCoveredFraction phaseMean
  exact div_nonneg (sum_nonneg (fun _ _ => by split_ifs <;> norm_num)) (by positivity)

/-- Conditional probability that the remaining moduli finish the fixed core. -/
noncomputable def coreCoverWeight (P R S : Finset ℕ) (r : Phase P) : ℝ :=
  populationCoveredFraction (populationSurvivors S P r) R

lemma coreCoverWeight_nonneg (P R S : Finset ℕ) (r : Phase P) :
    0 ≤ coreCoverWeight P R S r := populationCoveredFraction_nonneg _ _

lemma coreCoverWeight_mean (P R S : Finset ℕ) (hdis : Disjoint P R) :
    phaseMean P (coreCoverWeight P R S) = populationCoveredFraction S (P ∪ R) :=
  (population_cover_union S P R hdis).symm

lemma populationSurvivors_union_population (P S T : Finset ℕ) (r : Phase P) :
    populationSurvivors (S ∪ T) P r =
      populationSurvivors S P r ∪ populationSurvivors T P r := by
  exact filter_union _ _ _

/-- This is pointwise in the core phase. Only the remaining one-hit moduli are
averaged; the two core survivor populations are not assumed independent. -/
theorem coreCoverWeight_union_le (P R S T : Finset ℕ) (m : ℕ)
    (hR : ∀ p ∈ R, 0 < p ∧ m ≤ p)
    (hS : S ⊆ range m) (hT : T ⊆ range m) (hST : Disjoint S T) (r : Phase P) :
    coreCoverWeight P R (S ∪ T) r ≤ coreCoverWeight P R S r * coreCoverWeight P R T r := by
  unfold coreCoverWeight
  rw [populationSurvivors_union_population]
  exact disjoint_population_coverage R _ _ m hR
    ((filter_subset _ _).trans hS) ((filter_subset _ _).trans hT)
    (hST.mono (filter_subset _ _) (filter_subset _ _))

/-- Exact joint-core upper bound on the combined coverage probability. -/
theorem population_cover_le_core_correlation (P R S T : Finset ℕ) (m : ℕ)
    (hPR : Disjoint P R) (hR : ∀ p ∈ R, 0 < p ∧ m ≤ p)
    (hS : S ⊆ range m) (hT : T ⊆ range m) (hST : Disjoint S T) :
    populationCoveredFraction (S ∪ T) (P ∪ R) ≤
      phaseMean P (fun r => coreCoverWeight P R S r * coreCoverWeight P R T r) := by
  rw [← coreCoverWeight_mean P R (S ∪ T) hPR]
  exact phaseMean_mono P (coreCoverWeight_union_le P R S T m hR hS hT hST)

/-- A finite-phase correlation bound. The complete core phase count is retained,
not replaced by the number of primes or by an absolute constant. -/
lemma phaseMean_product_le_phase_mass (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f g : Phase P → ℝ) (hf : ∀ r, 0 ≤ f r) (hg : ∀ r, 0 ≤ g r) :
    phaseMean P (fun r => f r*g r) ≤
      (∏ p ∈ P, (p : ℝ))*phaseMean P f*phaseMean P g := by
  let D : ℝ := ∏ p : P, (p.val : ℝ)
  have hD : 0 < D := prod_pos (fun p _ => by exact_mod_cast (hP p.val p.property).pos)
  have he : (∏ p ∈ P, (p : ℝ)) = D := (prod_coe_sort P (fun p : ℕ => (p : ℝ))).symm
  have hs : (∑ r : Phase P, f r*g r) ≤ (∑ r : Phase P, f r)*(∑ r : Phase P, g r) := by
    rw [sum_mul]
    apply sum_le_sum
    intro r hr
    exact mul_le_mul_of_nonneg_left (single_le_sum (fun t _ => hg t) (mem_univ r)) (hf r)
  rw [he]
  change (∑ r, f r*g r)/D ≤ D*((∑ r, f r)/D)*((∑ r, g r)/D)
  calc
    _ ≤ ((∑ r, f r)*(∑ r, g r))/D := div_le_div_of_nonneg_right hs hD.le
    _ = _ := by field_simp

/-- The unconditional finite-core loss is the product of its primes. This is
only a restricted one-hit-tail bound, not the conjectured sublinear-power loss. -/
theorem population_cover_le_core_phase_mass (P R S T : Finset ℕ) (m : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hPR : Disjoint P R)
    (hR : ∀ p ∈ R, 0 < p ∧ m ≤ p)
    (hS : S ⊆ range m) (hT : T ⊆ range m) (hST : Disjoint S T) :
    populationCoveredFraction (S ∪ T) (P ∪ R) ≤
      (∏ p ∈ P, (p : ℝ))*populationCoveredFraction S (P ∪ R)*
        populationCoveredFraction T (P ∪ R) := by
  have hh := (population_cover_le_core_correlation P R S T m hPR hR hS hT hST).trans
    (phaseMean_product_le_phase_mass P hP (coreCoverWeight P R S) (coreCoverWeight P R T)
      (coreCoverWeight_nonneg P R S) (coreCoverWeight_nonneg P R T))
  simpa only [coreCoverWeight_mean P R S hPR,coreCoverWeight_mean P R T hPR] using hh

/-- A second-moment form that avoids the coarse complete phase count. Its
right-hand side still involves the actual, generally nonconstant core weights. -/
theorem population_cover_le_core_square_mean (P R S T : Finset ℕ) (m : ℕ)
    (hPR : Disjoint P R) (hR : ∀ p ∈ R, 0 < p ∧ m ≤ p)
    (hS : S ⊆ range m) (hT : T ⊆ range m) (hST : Disjoint S T) :
    populationCoveredFraction (S ∪ T) (P ∪ R) ≤
      (phaseMean P (fun r => coreCoverWeight P R S r^2)+
        phaseMean P (fun r => coreCoverWeight P R T r^2))/2 := by
  have hh := population_cover_le_core_correlation P R S T m hPR hR hS hT hST
  have hs := phaseMean_mono P (fun r =>
    show coreCoverWeight P R S r*coreCoverWeight P R T r ≤
      (coreCoverWeight P R S r^2+coreCoverWeight P R T r^2)/2 by
        nlinarith only [sq_nonneg (coreCoverWeight P R S r-coreCoverWeight P R T r)])
  rw [phaseMean_div,phaseMean_add] at hs
  exact hh.trans hs

#print axioms population_cover_le_core_correlation
#print axioms population_cover_le_core_phase_mass
#print axioms population_cover_le_core_square_mean
end Erdos970.OneHitLogConcavity
