import Submission.HarmonicStableSkewZero

/-! Harmonic density one half for consecutive largest-prime-factor rises.
This is a weaker theorem than the natural-density conjecture in Spec.lean;
no reverse Tauberian implication is used or asserted. -/
namespace Erdos371
open Finset Filter FiniteInformation DilationSpectrum
open scoped Topology
set_option autoImplicit false

lemma localFactorSign_harmonic_mean_zero (Q : ℕ) :
    Tendsto (fun N => harmonicMean (N+1) (localFactorSign Q)) atTop (𝓝 0) :=
  stable_finite_labels_harmonic_skew_zero (localPrimeLabel Q)
    (localPrimeLabel_mean_dilation_defect_zero Q) orderSkew orderSkew_swap orderSkew_abs_le

/-- The actual largest-prime comparison sign has zero harmonic mean. -/
theorem factorSign_harmonic_mean_zero :
    Tendsto (fun N => harmonicMean (N+1) factorSign) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨Q,hQ,happrox⟩ := localFactorSign_harmonic_approximation (ε/2) (by positivity)
  have hz := (localFactorSign_harmonic_mean_zero Q).abs
  filter_upwards [happrox Q le_rfl,hz.eventually_lt_const (show |(0 : ℝ)|<ε/2 by simpa using half_pos hε)]
    with N happrox hsmall
  have herr := (harmonicMean_abs_difference_le N factorSign (localFactorSign Q)).trans happrox
  have ht := abs_sub_le (harmonicMean (N+1) factorSign) (harmonicMean (N+1) (localFactorSign Q)) 0
  rw [Real.dist_eq,sub_zero]
  simp only [sub_zero] at ht
  linarith

lemma harmonicMean_one (N : ℕ) : harmonicMean (N+1) (fun _ => (1 : ℝ)) = 1 := by
  simpa only [harmonicMean,harmonicWeight,← sum_div] using harmonicWeight_sum N

/-- Precisely one half in harmonic averages. The natural-density statement
in Spec.lean remains a distinct, stronger claim. -/
theorem largest_prime_rises_harmonic_half :
    Tendsto (fun N : ℕ => harmonicMean (N+1)
      (fun n => if Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n then (1 : ℝ) else 0)) atTop (𝓝 (1/2)) := by
  let R (n : ℕ) : ℝ := if Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n then 1 else 0
  have he (n : ℕ) : factorSign n = 2*R n-1 := by
    unfold factorSign predicateSign R
    split_ifs <;> norm_num
  have hm (N : ℕ) : harmonicMean (N+1) R = (harmonicMean (N+1) factorSign+1)/2 := by
    have hh : harmonicMean (N+1) factorSign = 2*harmonicMean (N+1) R-1 := by
      rw [show factorSign=(fun n => 2*R n-1) from funext he,
        harmonicMean_sub,harmonicMean_const_mul,harmonicMean_one]
    linarith
  have ht := (factorSign_harmonic_mean_zero.add_const 1).div_const 2
  simp only [zero_add] at ht
  simpa only [← hm] using ht

#print axioms factorSign_harmonic_mean_zero
#print axioms largest_prime_rises_harmonic_half
end Erdos371
