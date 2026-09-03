import Submission.UniformWitnessResidueExplore
import Submission.ResidueProjectionDensityExplore

/-! Uniform ordinary-prefix residue energy. The modulus may depend on the
cutoff; these remain mean-square rather than pointwise conclusions. -/
namespace Erdos66UniformResiduePrefix
open Erdos66UniformWitnessResidue Erdos66ResidueProjectionDensity
  Erdos66NaturalResidueProjection Erdos66AbelSquarePrefix Erdos66TauberianProfile
  Erdos66WitnessAutocorrelation Erdos66Generating Erdos66ResidueSeries
  Erdos66WitnessResidueProjection
open Filter AdditiveCombinatorics
open scoped Classical Topology
set_option maxHeartbeats 2400000

noncomputable def prefixEnergy (m : ℕ) [NeZero m] (A : Set ℕ) (N : ℕ) : ℝ :=
  (∑ n∈Finset.range N, totalError m A n^2)/((N : ℝ)*(Real.log N)^2)

noncomputable def prefixEnvelope (A : Set ℕ) (c : ℝ) (N : ℕ) : ℝ :=
  envelope A c (radius N)/(radius N)^N

lemma prefixEnergy_nonneg (m : ℕ) [NeZero m] (A : Set ℕ) (N : ℕ) :
    0 ≤ prefixEnergy m A N := by
  exact div_nonneg (Finset.sum_nonneg (fun n _ ↦ sq_nonneg _))
    (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

lemma unshifted_prefix_bound (f : ℕ → ℝ) (hf : ∀ n, 0≤f n) (N : ℕ)
    {r : ℝ} (hr0 : 0≤r) (hr1 : r≤1) (hs : Summable (fun n ↦ f n*r^n)) :
    (∑ n∈Finset.range N, f n)*r^N ≤ series f r := by
  calc
    _ = ∑ n∈Finset.range N, f n*r^N := Finset.sum_mul ..
    _ ≤ ∑ n∈Finset.range N, f n*r^n := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hr0 hr1 (Finset.mem_range.mp hn).le) (hf n)
    _ ≤ _ := hs.sum_le_tsum _ (fun n _ ↦ mul_nonneg (hf n) (pow_nonneg hr0 n))

lemma prefixEnergy_le_abel (m : ℕ) [NeZero m] (A : Set ℕ) {N : ℕ} (hN : 2≤N) :
    prefixEnergy m A N ≤
      (residueEnergy m (indicator A) (radius N)*squareKernel (radius N))/(radius N)^N := by
  have hr := radius_bounds hN
  have hb := mul_le_mul_of_nonneg_right
    (unshifted_prefix_bound (fun n ↦ totalError m A n^2) (fun n ↦ sq_nonneg _) N
      hr.1.le hr.2.le (summable_totalError_square m A hr.1 hr.2))
    (squareKernel_nonneg hr.2)
  rw [totalError_series_eq m A hr.1 hr.2] at hb
  apply (le_div_iff₀ (pow_pos hr.1 N)).mpr
  simpa only [prefixEnergy,squareKernel_radius,div_eq_mul_inv,one_div,one_mul,mul_assoc,mul_left_comm,mul_comm] using hb

lemma prefixEnvelope_tendsto {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (prefixEnvelope A c) atTop (𝓝 0) := by
  have hh := ((envelope_tendsto h).comp radius_tendsto).div radius_pow_tendsto (Real.exp_ne_zero _)
  simpa only [prefixEnvelope,Function.comp_apply,zero_div] using hh

lemma prefixEnergy_le_envelope {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    ∀ᶠ N in atTop, ∀ (m : ℕ) [NeZero m], prefixEnergy m A N ≤ prefixEnvelope A c N := by
  have hL := radius_tendsto.eventually (negative_log_one_sub.eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop 2,hL] with N hN hLN
  intro m hm
  have hr := radius_bounds hN
  exact (prefixEnergy_le_abel m A hN).trans
    (div_le_div_of_nonneg_right
      (normalized_residueEnergy_le_envelope m A (Erdos66Explore.limit_nonneg h) hr.1 hr.2 hLN)
      (pow_nonneg hr.1.le N))

/-- The cutoff threshold precedes the choice of positive modulus. -/
theorem witness_uniform_prefix_energy_zero {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    ∀ ε>0, ∀ᶠ N in atTop, ∀ (m : ℕ) [NeZero m], prefixEnergy m A N<ε := by
  intro ε hε
  filter_upwards [prefixEnergy_le_envelope h,(prefixEnvelope_tendsto h).eventually_lt_const hε]
    with N hb hN
  exact fun m hm ↦ (hb m).trans_lt hN

/-- An arbitrary cutoff-dependent choice of modulus is allowed. -/
theorem witness_variable_prefix_energy_zero {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (μ : ℕ → ℕ) [∀ N, NeZero (μ N)] :
    Tendsto (fun N ↦ prefixEnergy (μ N) A N) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun N ↦ prefixEnergy_nonneg (μ N) A N))
    _ (prefixEnvelope_tendsto h)
  filter_upwards [prefixEnergy_le_envelope h] with N hN
  exact hN (μ N)

end Erdos66UniformResiduePrefix
