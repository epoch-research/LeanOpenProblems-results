import Submission.ResampledLowCountCylinder
import Submission.FilteredExposureBarrier

/-! Exact combination of resampling and soft exposure. The analytic inputs
remain premises. A separate algebraic lemma records a limitation of replacing
the factorial exposure budget by a coarse reciprocal-sum power. -/
namespace Erdos970.SoftExposure
open Finset Real GapAverages

/-- All probability and exposure factors are retained in this necessary
inequality for a covered phase. -/
theorem resampled_exposure_necessary (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (m j : ℕ) (A b D : ℝ)
    (hA : 0 < A) (hb : 0 < b) (hbA : b ≤ A)
    (hpartial : ∀ r : Phase P, PartialLower j (range m) P (phaseResidues P r) A)
    (r : Phase P) (hr : intervalCount P m r = 0)
    (hD : filteredDeletionBudget P Q hQP m r ≤ D) :
    (1-b/A)^j * ((1-D*density (P \ Q)/b) * (∏ q ∈ Q, (q : ℝ)⁻¹)) ≤
      (j.factorial : ℝ) * ∑ T ∈ P.powersetCard j, ∏ p ∈ T, (p : ℝ)⁻¹ := by
  have hbase : 0 ≤ 1-b/A := sub_nonneg.mpr ((div_le_one hA).mpr hbA)
  exact (mul_le_mul_of_nonneg_left
    (lowCountFraction_markov_lower_filtered P Q hQP hP m b D hb r hr hD)
    (pow_nonneg hbase j)).trans
    (lowCountFraction_factorial_symmetric P hP m j A b hA hb.le hbA hpartial)

/-- A strict inequality in the opposite direction would exclude the cover.
No such parameter estimate is being asserted by this conditional theorem. -/
theorem no_cover_of_resampled_exposure (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (m j : ℕ) (A b D : ℝ)
    (hA : 0 < A) (hb : 0 < b) (hbA : b ≤ A)
    (hpartial : ∀ r : Phase P, PartialLower j (range m) P (phaseResidues P r) A)
    (hstrict : (j.factorial : ℝ) * ∑ T ∈ P.powersetCard j, ∏ p ∈ T, (p : ℝ)⁻¹ <
      (1-b/A)^j * ((1-D*density (P \ Q)/b) * (∏ q ∈ Q, (q : ℝ)⁻¹)))
    (r : Phase P) (hD : filteredDeletionBudget P Q hQP m r ≤ D) :
    intervalCount P m r ≠ 0 := by
  intro hr
  exact hstrict.not_ge (resampled_exposure_necessary P Q hQP hP m j A b D
    hA hb hbA hpartial r hr hD)

/-- If the retained core is below the exposure depth, a covering phase
forces its filtered budget to be at least the partial-count floor. -/
lemma partial_floor_le_filtered_budget (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (m j : ℕ) (A : ℝ) (hQj : Q.card < j) (r : Phase P)
    (hpartial : PartialLower j (range m) P (phaseResidues P r) A)
    (hr : intervalCount P m r = 0) :
    A ≤ filteredDeletionBudget P Q hQP m r :=
  (partial_lower_core_count P Q hQP m j A r hpartial hQj).trans
    (core_count_le_filteredDeletionBudget P Q hQP m r hr)

/-- A purely algebraic limitation of a coarse power budget. If the core
count bound D is at least A and 1-rho <= sigma, the Markov-cylinder expression
cannot exceed sigma^j. This does NOT bound the exact factorial budget below. -/
theorem markov_expression_le_coarse_power (A b D rho w sigma : ℝ) (j : ℕ)
    (hA : 0 < A) (hb : 0 < b) (hbA : b ≤ A) (hAD : A ≤ D)
    (hrho : 0 ≤ rho) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hsigma : 0 ≤ sigma) (hrhosigma : 1-rho ≤ sigma) :
    (1-b/A)^j * ((1-D*rho/b)*w) ≤ sigma^j := by
  have hbase : 0 ≤ 1-b/A := sub_nonneg.mpr ((div_le_one hA).mpr hbA)
  have hD : 0 ≤ D := hA.le.trans hAD
  have hc1 : 1-D*rho/b ≤ 1 := by
    have hh : 0 ≤ D*rho/b := div_nonneg (mul_nonneg hD hrho) hb.le
    linarith
  by_cases hc : 1-D*rho/b ≤ 0
  · exact (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hbase j)
      (mul_nonpos_of_nonpos_of_nonneg hc hw)).trans (pow_nonneg hsigma j)
  · have hcpos : 0 < 1-D*rho/b := lt_of_not_ge hc
    have hDrho : D*rho < b := (div_lt_one hb).mp (by linarith only [hcpos])
    have hArho : A*rho < b := (mul_le_mul_of_nonneg_right hAD hrho).trans_lt hDrho
    have hratio : rho < b/A := (lt_div_iff₀ hA).mpr (by simpa only [mul_comm] using hArho)
    have hbs : 1-b/A ≤ sigma := (by linarith only [hratio,hrhosigma])
    have hcw : (1-D*rho/b)*w ≤ 1 := by
      exact (mul_le_mul_of_nonneg_left hw1 hcpos.le).trans (by simpa using hc1)
    exact (mul_le_of_le_one_right (pow_nonneg hbase j) hcw).trans
      (pow_le_pow_left₀ hbase hbs j)

/-- For a large retained core even the EXACT factorial budget is already
at least this resampling-cylinder expression. -/
theorem markov_expression_le_budget_of_large_core (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (j : ℕ) (hjQ : j ≤ Q.card)
    (A b D : ℝ) (hA : 0 < A) (hb : 0 < b) (hbA : b ≤ A) (hD : 0 ≤ D) :
    (1-b/A)^j * ((1-D*density (P \ Q)/b)*(∏ q ∈ Q, (q : ℝ)⁻¹)) ≤ budget j P := by
  have hw : 0 ≤ ∏ q ∈ Q, (q : ℝ)⁻¹ := prod_nonneg (fun _ _ => by positivity)
  have hbase : 0 ≤ 1-b/A := sub_nonneg.mpr ((div_le_one hA).mpr hbA)
  have hbase1 : 1-b/A ≤ 1 := by have := div_nonneg hb.le hA.le; linarith
  have hrho : 0 ≤ density (P \ Q) := (density_pos _
    (fun p hp => hP p (Finset.mem_sdiff.mp hp).1)).le
  have hc1 : 1-D*density (P \ Q)/b ≤ 1 := by
    have := div_nonneg (mul_nonneg hD hrho) hb.le
    linarith
  have hfac : (1 : ℝ) ≤ j.factorial := by exact_mod_cast Nat.factorial_pos j
  calc
    _ ≤ (1-b/A)^j * (∏ q ∈ Q, (q : ℝ)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hbase j)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 hw
    _ ≤ ∏ q ∈ Q, (q : ℝ)⁻¹ := mul_le_of_le_one_left hw (pow_le_one₀ hbase hbase1)
    _ ≤ (j.factorial : ℝ) * (∏ q ∈ Q, (q : ℝ)⁻¹) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hfac hw
    _ ≤ budget j P := factorial_cylinder_weight_le_budget P Q hQP hP j hjQ

#print axioms resampled_exposure_necessary
#print axioms no_cover_of_resampled_exposure
#print axioms markov_expression_le_coarse_power
#print axioms markov_expression_le_budget_of_large_core
end Erdos970.SoftExposure
