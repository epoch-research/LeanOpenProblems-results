import Submission.UniformResidueProfileExplore

/-! Uniform-in-modulus residue energy for a hypothetical witness. The
modulus may vary arbitrarily with the radius. No pointwise splitting of
individual representation counts is asserted. -/
namespace Erdos66UniformWitnessResidue
open Erdos66UniformResidueProfile Erdos66NaturalResidueProjection
  Erdos66WitnessResidueProjection Erdos66WitnessAutocorrelation
  Erdos66WitnessTwistedEnergy Erdos66AutocorrelationAbel Erdos66Generating
  Erdos66Fractional Erdos66FractionalFourthPower Erdos66SquareRootFluctuation
  Erdos66AbelErrorEnergy Erdos66ResidueSeries Erdos66WeightedSquareStability
open scoped Classical Topology
open Filter AdditiveCombinatorics
set_option maxHeartbeats 2800000

section Modulus
variable (m : ℕ) [NeZero m]

theorem residueEnergy_uniform_bound (A : Set ℕ) {c r : ℝ} (hc : 0 ≤ c) (hr0 : 0<r) (hr1 : r<1) :
    residueEnergy m (indicator A) r ≤ 4*c^2*series (fun n ↦ (harmonic (n+1) : ℝ)) r+
      Real.sqrt (series (errorSq A c) r*(4*series (errorSq A c) r+6*c^2*harmonicSqSeries r)) := by
  let q := Real.sqrt r
  have hq0 : 0<q := Real.sqrt_pos.mpr hr0
  have hq1 : q<1 := (Real.sqrt_lt' (by norm_num : (0:ℝ)<1)).mpr (by simpa using hr1)
  have hq2 : q^2=r := Real.sq_sqrt hr0.le
  have hf := summable_indicator A (r := q) (by simpa only [abs_of_pos hq0] using hq1)
  have hg : Summable (fun n ↦ (Real.sqrt c*profile n)*q^n) := by
    simpa only [pow_one,mul_assoc] using
      (summable_profile_power_weighted hq0.le hq1 1).mul_left (Real.sqrt c)
  have hh := natVariance_difference_sq m hf hg
  rw [natVariance_weighted,natVariance_weighted,convolution_error_weighted,
    natEnergy_weighted,natEnergy_weighted,hq2] at hh
  have hcA (n : ℕ) : sumConv (indicator A) (indicator A) n=(sumRep A n : ℝ) := sum_indicator_antidiagonal A n
  simp only [hcA,scaled_profile_convolution hc,mul_pow] at hh
  change (residueEnergy m (indicator A) r-residueEnergy m (fun n ↦ Real.sqrt c*profile n) r)^2 ≤
    series (errorSq A c) r*(2*series (fun n ↦ (sumRep A n : ℝ)^2) r+
      2*series (fun n ↦ c^2*(harmonic (n+1) : ℝ)^2) r) at hh
  have hgser : series (fun n ↦ c^2*(harmonic (n+1) : ℝ)^2) r=c^2*harmonicSqSeries r := by
    simp only [series,harmonicSqSeries,mul_assoc,tsum_mul_left]
  rw [hgser] at hh
  have hE0 : 0 ≤ series (errorSq A c) r :=
    tsum_nonneg (fun n ↦ mul_nonneg (sq_nonneg _) (pow_nonneg hr0.le n))
  have hsum : 2*series (fun n ↦ (sumRep A n : ℝ)^2) r+2*(c^2*harmonicSqSeries r) ≤
      4*series (errorSq A c) r+6*c^2*harmonicSqSeries r := by
    linarith [representation_square_series_bound A c hr0.le hr1]
  have hs := Real.le_sqrt_of_sq_le (hh.trans (mul_le_mul_of_nonneg_left hsum hE0))
  have hv := fractional_residueEnergy_uniform m hc hr0.le hr1
  linarith

end Modulus


lemma harmonic_shift_squareKernel_zero :
    Tendsto (fun r ↦ series (fun n ↦ (harmonic (n+1) : ℝ)) r*squareKernel r)
      (𝓝[<] 1) (𝓝 0) := by
  have hh := (logarithmic_abelian_limit harmonic_shift_log_ratio
    (fun r hr0 hr1 ↦ summable_harmonic_shift hr0.le hr1)).mul
      (negative_log_one_sub.const_div_atTop (1 : ℝ))
  simp only [mul_zero] at hh
  apply hh.congr
  intro r
  dsimp only [squareKernel]
  ring

noncomputable def envelope (A : Set ℕ) (c r : ℝ) : ℝ :=
  4*c^2*series (fun n ↦ (harmonic (n+1) : ℝ)) r*squareKernel r+
    Real.sqrt ((series (errorSq A c) r*squareKernel r)*
      (4*(series (errorSq A c) r*squareKernel r)+36*c^2))

lemma envelope_tendsto {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (envelope A c) (𝓝[<] 1) (𝓝 0) := by
  have hE := witness_normalized_error_energy_zero h
  have hH := harmonic_shift_squareKernel_zero.const_mul (4*c^2)
  have hh := hH.add ((hE.mul ((hE.const_mul 4).add_const (36*c^2))).sqrt)
  change Tendsto (fun r ↦ envelope A c r) _ _
  simpa only [envelope,mul_assoc,mul_zero,zero_mul,zero_add,Real.sqrt_zero,add_zero] using hh

/-- One scalar bound works simultaneously for every positive modulus. -/
theorem normalized_residueEnergy_le_envelope (m : ℕ) [NeZero m] (A : Set ℕ) {c r : ℝ}
    (hc : 0≤c) (hr0 : 0<r) (hr1 : r<1) (hL : 1≤-Real.log (1-r)) :
    residueEnergy m (indicator A) r*squareKernel r ≤ envelope A c r := by
  let E := series (errorSq A c) r*squareKernel r
  have hk := squareKernel_nonneg hr1
  have he0 : 0 ≤ series (errorSq A c) r :=
    tsum_nonneg (fun n ↦ mul_nonneg (sq_nonneg _) (pow_nonneg hr0.le n))
  have hEK : 0≤E := mul_nonneg he0 hk
  have hh := mul_le_mul_of_nonneg_right (residueEnergy_uniform_bound m A hc hr0 hr1) hk
  rw [add_mul,sqrt_multiply_kernel _ _ _ hk] at hh
  have hs : Real.sqrt ((series (errorSq A c) r*squareKernel r)*
      ((4*series (errorSq A c) r+6*c^2*harmonicSqSeries r)*squareKernel r)) ≤
      Real.sqrt (E*(4*E+36*c^2)) := by
    apply Real.sqrt_le_sqrt
    change E*((4*series (errorSq A c) r+6*c^2*harmonicSqSeries r)*squareKernel r) ≤ _
    apply mul_le_mul_of_nonneg_left _ hEK
    have hmul := mul_le_mul_of_nonneg_left (harmonicSqSeries_normalized_bound hr0 hr1 hL)
      (by positivity : 0≤6*c^2)
    dsimp only [E]
    nlinarith
  dsimp only [envelope]
  linarith

/-- Uniform quantifiers: the neighborhood is chosen before the modulus. -/
theorem witness_all_moduli_energy_zero {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    ∀ ε>0, ∀ᶠ r in 𝓝[<] 1, ∀ (m : ℕ) [NeZero m],
      residueEnergy m (indicator A) r*squareKernel r<ε := by
  intro ε hε
  filter_upwards [(envelope_tendsto h).eventually_lt_const hε,unit_interval_eventually,
    negative_log_one_sub.eventually_ge_atTop 1] with r he hr hL
  intro m hm
  exact (normalized_residueEnergy_le_envelope m A (Erdos66Explore.limit_nonneg h) hr.1 hr.2 hL).trans_lt he

/-- In particular the modulus may change arbitrarily with the radius;
there is no growth-rate or continuity hypothesis on that choice. -/
theorem witness_variable_modulus_energy_zero {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (μ : ℝ → ℕ) [∀ r, NeZero (μ r)] :
    Tendsto (fun r ↦ residueEnergy (μ r) (indicator A) r*squareKernel r)
      (𝓝[<] 1) (𝓝 0) := by
  apply squeeze_zero' _ _ (envelope_tendsto h)
  · filter_upwards [unit_interval_eventually] with r hr
    exact mul_nonneg (residueEnergy_nonneg (μ r) _ hr.1.le) (squareKernel_nonneg hr.2)
  · filter_upwards [unit_interval_eventually,negative_log_one_sub.eventually_ge_atTop 1] with r hr hL
    exact normalized_residueEnergy_le_envelope (μ r) A (Erdos66Explore.limit_nonneg h) hr.1 hr.2 hL

end Erdos66UniformWitnessResidue

