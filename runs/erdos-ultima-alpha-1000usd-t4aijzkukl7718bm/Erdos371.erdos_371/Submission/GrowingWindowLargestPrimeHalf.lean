import Submission.ShiftedStableSkewZero

/-! The actual largest-prime-factor comparison has harmonic density one half
uniformly on intervals of growing harmonic mass. This does not cover intervals
of fixed multiplicative ratio and does not settle the natural-density claim. -/
namespace Erdos371.FiniteInformation
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma shiftedHarmonicMean_eventual_upper_of_prefix_upper (F : ℕ → ℝ)
    (hF : ∀ n, 0 ≤ F n ∧ F n ≤ 2) (η : ℝ) (hη : 0 ≤ η)
    (hmean : ∀ᶠ N : ℕ in atTop, prefixMean N F ≤ η)
    (ε : ℝ) (hε : 0 < ε) (A M : ℕ → ℕ)
    (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop) :
    ∀ᶠ j : ℕ in atTop, shiftedHarmonicMean (A j) (M j) F ≤ η+ε := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp hmean
  have hbound (N : ℕ) : (∑ n ∈ range N, F n) ≤ η*N+2*K := by
    by_cases hN : N=0
    · subst N; simp
    by_cases hNK : K ≤ N
    · have hNr : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
      have hs := (div_le_iff₀ hNr).mp (hK N hNK)
      change (∑ n ∈ range N, F n) ≤ η*N at hs
      linarith [Nat.cast_nonneg (α := ℝ) K]
    · have hs : (∑ n ∈ range N, F n) ≤ 2*N := by
        simpa only [sum_const,card_range,nsmul_eq_mul,mul_comm] using
          (sum_le_sum (s := range N) (fun n _ => (hF n).2))
      have hnK : (N : ℝ) ≤ K := by exact_mod_cast (by omega : N ≤ K)
      have he : 0 ≤ η*(N : ℝ) := mul_nonneg hη (Nat.cast_nonneg N)
      linarith
  have ht : Tendsto (fun j => (η+2*K)/shiftedHarmonicMass (A j) (M j)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hH
  filter_upwards [ht.eventually_lt_const hε] with j hj
  have hb := shiftedHarmonicMean_of_prefix_bound F (fun n => (hF n).1) η (2*K)
    hη (by positivity) hbound (A j) (M j)
  linarith

end Erdos371.FiniteInformation
namespace Erdos371
open Finset Filter FiniteInformation DilationSpectrum
open scoped Topology
set_option autoImplicit false

lemma localFactorSign_shifted_harmonic_approximation (ε : ℝ) (hε : 0 < ε)
    (A M : ℕ → ℕ) (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop) :
    ∃ Q₀ > 0, ∀ Q ≥ Q₀, ∀ᶠ j : ℕ in atTop,
      shiftedHarmonicMean (A j) (M j) (fun n => |factorSign n-localFactorSign Q n|) ≤ ε := by
  obtain ⟨Q₀,hQ₀,happrox⟩ := localFactorSign_natural_approximation (ε/2) (by positivity)
  refine ⟨Q₀,hQ₀,?_⟩
  intro Q hQ
  simpa only [add_halves] using shiftedHarmonicMean_eventual_upper_of_prefix_upper
    (fun n => |factorSign n-localFactorSign Q n|)
    (fun n => ⟨abs_nonneg _,localFactorSign_error_le_two Q n⟩)
    (ε/2) (by positivity) (happrox Q hQ) (ε/2) (by positivity) A M hH

lemma localFactorSign_shifted_harmonic_zero (Q : ℕ) (A M : ℕ → ℕ)
    (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop) :
    Tendsto (fun j => shiftedHarmonicMean (A j) (M j) (localFactorSign Q)) atTop (𝓝 0) :=
  stable_finite_labels_shifted_harmonic_skew_zero (localPrimeLabel Q)
    (localPrimeLabel_mean_dilation_defect_zero Q) orderSkew orderSkew_swap orderSkew_abs_le A M hH

/-- Actual signed cancellation along every sequence of intervals of growing
harmonic mass, with no prescribed rate of growth or restriction on their origins. -/
theorem factorSign_growing_harmonic_window_zero (A M : ℕ → ℕ)
    (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop) :
    Tendsto (fun j => shiftedHarmonicMean (A j) (M j) factorSign) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨Q,hQ,happrox⟩ := localFactorSign_shifted_harmonic_approximation (ε/2) (by positivity) A M hH
  have hz := (localFactorSign_shifted_harmonic_zero Q A M hH).abs
  filter_upwards [happrox Q le_rfl,hz.eventually_lt_const
    (show |(0 : ℝ)|<ε/2 by simpa using half_pos hε)] with j ha hs
  have herr := (shiftedHarmonicMean_abs_difference_le (A j) (M j) factorSign (localFactorSign Q)).trans ha
  have ht := abs_sub_le (shiftedHarmonicMean (A j) (M j) factorSign)
    (shiftedHarmonicMean (A j) (M j) (localFactorSign Q)) 0
  rw [Real.dist_eq,sub_zero]
  simp only [sub_zero] at ht
  linarith

/-- Uniformity over ALL intervals, stated without endpoint sequences. Only
large harmonic mass is needed. This is not an unnormalized fixed-ratio estimate. -/
theorem factorSign_uniform_long_harmonic_windows (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ A M : ℕ, R ≤ shiftedHarmonicMass A M →
      |shiftedHarmonicMean A M factorSign| < ε := by
  by_contra h
  push_neg at h
  have hn (n : ℕ) : ∃ A M : ℕ, (n+1 : ℝ) ≤ shiftedHarmonicMass A M ∧
      ε ≤ |shiftedHarmonicMean A M factorSign| := h (n+1) (by positivity)
  choose A M hmass hbad using hn
  have hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop :=
    tendsto_atTop_mono hmass (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have ht := (factorSign_growing_harmonic_window_zero A M hH).abs
  obtain ⟨j,hj⟩ := (ht.eventually_lt_const (by simpa using hε : |(0 : ℝ)| < ε)).exists
  exact (not_lt_of_ge (hbad j)) hj

lemma shifted_rise_mean_identity (A M : ℕ) :
    shiftedHarmonicMean A M
      (fun n => if Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) then (1 : ℝ) else 0) =
        (shiftedHarmonicMean A M factorSign+1)/2 := by
  let F (n : ℕ) : ℝ := if Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) then 1 else 0
  have he (n : ℕ) : factorSign n=2*F n-1 := by
    unfold factorSign predicateSign F
    split_ifs <;> norm_num
  have hh : shiftedHarmonicMean A M factorSign = 2*shiftedHarmonicMean A M F-1 := by
    rw [show factorSign=(fun n => 2*F n-1) from funext he,
      shiftedHarmonicMean_sub,shiftedHarmonicMean_const_mul,shiftedHarmonicMean_const]
  change shiftedHarmonicMean A M F = _
  linarith

/-- Harmonic density one half on arbitrary intervals of diverging harmonic
mass. The natural density in Spec.lean is still a stronger assertion. -/
theorem largest_prime_rises_growing_harmonic_half (A M : ℕ → ℕ)
    (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop) :
    Tendsto (fun j => shiftedHarmonicMean (A j) (M j)
      (fun n => if Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) then (1 : ℝ) else 0)) atTop (𝓝 (1/2)) := by
  have ht := (factorSign_growing_harmonic_window_zero A M hH).add_const 1 |>.div_const 2
  simpa only [shifted_rise_mean_identity,zero_add] using ht

#print axioms factorSign_growing_harmonic_window_zero
#print axioms factorSign_uniform_long_harmonic_windows
#print axioms largest_prime_rises_growing_harmonic_half
end Erdos371
