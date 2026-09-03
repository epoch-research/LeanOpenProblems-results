import Submission.PrimeHarmonicDivergenceMass

/-! Uniform summability of the finite-endpoint divergence error. This concerns
the difference of winner and loser currents, not either vector separately. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma primeLabelIndicator_hasSum (m : ℕ) :
    HasSum (fun p => primeLabelIndicator p m) 1 := by
  simpa only [primeLabelIndicator, eq_comm] using
    (hasSum_ite_eq (Nat.maxPrimeFac m) (1 : ℝ))

lemma primeDivergenceTerm_label_hasSum (n : ℕ) :
    HasSum (fun p => primeDivergenceTerm p n) (reciprocalFluxStep n) := by
  simpa only [primeDivergenceTerm, one_mul] using
    (primeLabelIndicator_hasSum (n+2)).mul_right (reciprocalFluxStep n)

noncomputable def primeDivergenceRemainder (M p : ℕ) : ℝ :=
  primeDivergenceMass p - ∑ n ∈ range M, primeDivergenceTerm p n

lemma primeDivergenceRemainder_nonneg (M p : ℕ) :
    0 ≤ primeDivergenceRemainder M p := by
  apply sub_nonneg.mpr
  exact (primeDivergenceTerm_summable p).sum_le_tsum (range M)
    (fun n _ => primeDivergenceTerm_nonneg p n)

lemma primeDivergenceRemainder_hasSum (M : ℕ) :
    HasSum (primeDivergenceRemainder M) (1/(M+1 : ℝ)) := by
  have hfin : HasSum (fun p => ∑ n ∈ range M, primeDivergenceTerm p n)
      (∑ n ∈ range M, reciprocalFluxStep n) :=
    hasSum_sum (fun n (_ : n ∈ range M) => primeDivergenceTerm_label_hasSum n)
  have h := primeDivergenceMass_hasSum.sub hfin
  rw [reciprocalFluxStep_sum] at h
  convert h using 1
  ring

noncomputable def primeEndpointMass (M p : ℕ) : ℝ :=
  primeLabelIndicator p (M+2)/(M+1 : ℝ)

lemma primeEndpointMass_nonneg (M p : ℕ) : 0 ≤ primeEndpointMass M p :=
  div_nonneg (primeLabelIndicator_nonneg p (M+2)) (by positivity)

lemma primeEndpointMass_hasSum (M : ℕ) :
    HasSum (primeEndpointMass M) (1/(M+1 : ℝ)) := by
  simpa only [primeEndpointMass, div_eq_mul_inv, one_mul] using
    (primeLabelIndicator_hasSum (M+2)).mul_right ((M+1 : ℝ)⁻¹)

noncomputable def primeHarmonicFluxError (M p : ℕ) : ℝ :=
  (rawPrimeWinnerHarmonic p (M+2) - rawPrimeLoserHarmonic p (M+2)) -
    (primeWinnerHarmonicLimit p - primeLoserHarmonicLimit p)

lemma primeHarmonicFluxError_eq (M p : ℕ) :
    primeHarmonicFluxError M p = primeEndpointMass M p - primeDivergenceRemainder M p := by
  rw [primeHarmonicFluxError, rawPrimeHarmonic_flux, primeHarmonicLimit_flux_exact]
  dsimp [primeEndpointMass, primeDivergenceRemainder, primeDivergenceTerm, reciprocalFluxStep]
  ring

lemma primeHarmonicFluxError_summable (M : ℕ) : Summable (primeHarmonicFluxError M) := by
  change Summable (fun p => primeHarmonicFluxError M p)
  simp_rw [primeHarmonicFluxError_eq]
  exact (primeEndpointMass_hasSum M).summable.sub (primeDivergenceRemainder_hasSum M).summable

/-- The full divergence vectors converge in l1 at a reciprocal endpoint rate. -/
theorem primeHarmonicFluxError_l1_bound (M : ℕ) :
    (∑' p, ‖primeHarmonicFluxError M p‖) ≤ 2/(M+1 : ℝ) := by
  have hb (p : ℕ) : ‖primeHarmonicFluxError M p‖ ≤
      primeEndpointMass M p + primeDivergenceRemainder M p := by
    rw [primeHarmonicFluxError_eq]
    exact (norm_sub_le _ _).trans_eq (by
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (primeEndpointMass_nonneg M p),
        abs_of_nonneg (primeDivergenceRemainder_nonneg M p)])
  have hs := (primeEndpointMass_hasSum M).add (primeDivergenceRemainder_hasSum M)
  have h := (primeHarmonicFluxError_summable M).norm.tsum_le_tsum hb hs.summable
  rw [hs.tsum_eq] at h
  exact h.trans_eq (by ring)

theorem primeHarmonicFluxError_l1_tendsto_zero :
    Tendsto (fun M => ∑' p, ‖primeHarmonicFluxError M p‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => tsum_nonneg (fun _ => norm_nonneg _))
    primeHarmonicFluxError_l1_bound
  simpa only [mul_zero, mul_one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2

#print axioms primeHarmonicFluxError_l1_bound
#print axioms primeHarmonicFluxError_l1_tendsto_zero
end Erdos371
