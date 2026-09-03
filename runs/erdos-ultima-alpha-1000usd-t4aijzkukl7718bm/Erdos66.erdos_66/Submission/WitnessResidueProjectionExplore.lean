import Submission.ResidueProfileProjectionExplore
import Submission.WitnessTwistedEnergyExplore

/-! Joint residue-projection variance is negligible for a hypothetical
logarithmic witness. These are mean-square, not pointwise, conclusions. -/
namespace Erdos66WitnessResidueProjection
open Erdos66NaturalResidueProjection Erdos66ResidueProfileProjection
  Erdos66WitnessAutocorrelation Erdos66WitnessTwistedEnergy Erdos66AutocorrelationAbel
  Erdos66Generating Erdos66Fractional Erdos66FractionalFourthPower
  Erdos66SquareRootFluctuation Erdos66AbelErrorEnergy Erdos66ResidueSeries
  Erdos66WeightedSquareStability
open scoped Classical Topology
open Filter AdditiveCombinatorics
set_option maxHeartbeats 2800000

lemma square_weight (x r : ℝ) (n : ℕ) : (x*r^n)^2=x^2*(r^2)^n := by
  rw [mul_pow,← pow_mul,Nat.mul_comm n 2,pow_mul]

lemma natEnergy_weighted (f g : ℕ → ℝ) (r : ℝ) :
    natEnergy (fun n ↦ f n*r^n) (fun n ↦ g n*r^n)=series (fun n ↦ sumConv f g n^2) (r^2) := by
  simp only [natEnergy,weighted_convolution,square_weight,series]

lemma convolution_error_weighted (f g : ℕ → ℝ) (r : ℝ) :
    (∑' n, (sumConv (fun n ↦ f n*r^n) (fun n ↦ f n*r^n) n-
      sumConv (fun n ↦ g n*r^n) (fun n ↦ g n*r^n) n)^2)=
      series (fun n ↦ (sumConv f f n-sumConv g g n)^2) (r^2) := by
  simp only [weighted_convolution,← sub_mul,square_weight,series]

lemma sumConv_scale (a : ℝ) (f g : ℕ → ℝ) (n : ℕ) :
    sumConv (fun n ↦ a*f n) (fun n ↦ a*g n) n=a^2*sumConv f g n := by
  unfold sumConv
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  ring

lemma residueTerm_scale (m : ℕ) [NeZero m] (a : ℝ) (f : ℕ → ℝ) (i : ZMod m) :
    residueTerm m (fun n ↦ a*f n) i=(fun n ↦ a*residueTerm m f i n) := by
  funext n
  unfold residueTerm
  split_ifs <;> simp

variable (m : ℕ) [NeZero m]

noncomputable def residueEnergy (f : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑ i : ZMod m, series (fun n ↦ projectionError m f i n^2) r

lemma residueEnergy_nonneg (f : ℕ → ℝ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ residueEnergy m f r :=
  Finset.sum_nonneg (fun i _ ↦ tsum_nonneg (fun n ↦ mul_nonneg (sq_nonneg _) (pow_nonneg hr n)))

lemma natVariance_weighted (f : ℕ → ℝ) (r : ℝ) :
    natVariance m (fun n ↦ f n*r^n)=residueEnergy m f (r^2) := by
  simp only [natVariance,projectionError_weighted,square_weight,residueEnergy,series]

lemma projectionError_scale (a : ℝ) (f : ℕ → ℝ) (i : ZMod m) (n : ℕ) :
    projectionError m (fun n ↦ a*f n) i n=a^2*projectionError m f i n := by
  rw [projectionError,residueTerm_scale,sumConv_scale,sumConv_scale]
  simp only [projectionError]
  ring

lemma projection_profile_square_bound {c : ℝ} (hc : 0 ≤ c) (i : ZMod m) (n : ℕ) :
    projectionError m (fun n ↦ Real.sqrt c*profile n) i n^2 ≤ 4*c^2*m^2 := by
  rw [projectionError_scale,Real.sq_sqrt hc,mul_pow]
  have hh := pow_le_pow_left₀ (abs_nonneg _) (projectionError_profile_bound m i n) 2
  rw [sq_abs,mul_pow] at hh
  nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg c)]

lemma summable_profile_projection_sq {c r : ℝ} (hc : 0 ≤ c) (hr0 : 0 ≤ r) (hr1 : r<1)
    (i : ZMod m) : Summable (fun n ↦ projectionError m (fun n ↦ Real.sqrt c*profile n) i n^2*r^n) := by
  apply ((summable_geometric_of_lt_one hr0 hr1).mul_left (4*c^2*m^2)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hr0 n))]
  exact mul_le_mul_of_nonneg_right (projection_profile_square_bound m hc i n) (pow_nonneg hr0 n)

lemma fractional_residueEnergy_bound {c r : ℝ} (hc : 0 ≤ c) (hr0 : 0 ≤ r) (hr1 : r<1) :
    residueEnergy m (fun n ↦ Real.sqrt c*profile n) r ≤ 4*c^2*m^3/(1-r) := by
  have hh (i : ZMod m) : series (fun n ↦ projectionError m (fun n ↦ Real.sqrt c*profile n) i n^2) r ≤
      (4*c^2*m^2)/(1-r) := by
    have ht := (summable_profile_projection_sq m hc hr0 hr1 i).tsum_le_tsum
      (fun n ↦ mul_le_mul_of_nonneg_right (projection_profile_square_bound m hc i n) (pow_nonneg hr0 n))
      ((summable_geometric_of_lt_one hr0 hr1).mul_left (4*c^2*m^2))
    simpa only [tsum_mul_left,tsum_geometric_of_lt_one hr0 hr1,div_eq_mul_inv] using ht
  calc
    _ ≤ ∑ _i : ZMod m, (4*c^2*m^2)/(1-r) := Finset.sum_le_sum (fun i _ ↦ hh i)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]; ring

lemma representation_square_series_bound (A : Set ℕ) (c : ℝ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r<1) :
    series (fun n ↦ (sumRep A n : ℝ)^2) r ≤
      2*series (errorSq A c) r+2*c^2*harmonicSqSeries r := by
  have hp (n : ℕ) : (sumRep A n : ℝ)^2*r^n ≤
      2*(errorSq A c n*r^n)+(2*c^2)*((harmonic (n+1) : ℝ)^2*r^n) := by
    have hsq : (sumRep A n : ℝ)^2 ≤ 2*errorSq A c n+2*c^2*(harmonic (n+1) : ℝ)^2 := by
      dsimp [errorSq]
      nlinarith [sq_nonneg ((sumRep A n : ℝ)-2*c*(harmonic (n+1) : ℝ))]
    nlinarith [mul_le_mul_of_nonneg_right hsq (pow_nonneg hr0 n)]
  have hs := summable_errorSq A 0 hr0 hr1
  simp only [errorSq,zero_mul,sub_zero] at hs
  have ht := hs.tsum_le_tsum hp (((summable_errorSq A c hr0 hr1).mul_left 2).add
    ((summable_harmonic_sq hr0 hr1).mul_left (2*c^2)))
  simpa only [Summable.tsum_add ((summable_errorSq A c hr0 hr1).mul_left 2)
    ((summable_harmonic_sq hr0 hr1).mul_left (2*c^2)),tsum_mul_left,series,harmonicSqSeries] using ht

/-- The quantitative projection-variance bound holds for every set A. -/
theorem residueEnergy_bound (A : Set ℕ) {c r : ℝ} (hc : 0 ≤ c) (hr0 : 0<r) (hr1 : r<1) :
    residueEnergy m (indicator A) r ≤ 4*c^2*m^3/(1-r)+
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
  have hv := fractional_residueEnergy_bound m hc hr0.le hr1
  linarith

/-- Every fixed residue projection has vanishing aggregate mean-square
error about its 1/m share of the total representation count. -/
theorem witness_residueEnergy_zero {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun r : ℝ ↦ residueEnergy m (indicator A) r*squareKernel r)
      (𝓝[<] 1) (𝓝 0) := by
  have hc := Erdos66Explore.limit_nonneg h
  let E : ℝ → ℝ := fun r ↦ series (errorSq A c) r*squareKernel r
  have hE : Tendsto E (𝓝[<] 1) (𝓝 0) := witness_normalized_error_energy_zero h
  have hlog : Tendsto (fun r : ℝ ↦ 4*c^2*m^3/(-Real.log (1-r))^2) (𝓝[<] 1) (𝓝 0) := by
    simpa only [div_pow,one_pow,mul_one_div,zero_pow (by decide : 2≠0),mul_zero] using
      ((negative_log_one_sub.const_div_atTop (1 : ℝ)).pow 2).const_mul (4*c^2*m^3)
  have hbound : Tendsto (fun r : ℝ ↦ 4*c^2*m^3/(-Real.log (1-r))^2+
      Real.sqrt (E r*(4*E r+36*c^2))) (𝓝[<] 1) (𝓝 0) := by
    simpa only [mul_zero,zero_mul,zero_add,Real.sqrt_zero,add_zero] using
      hlog.add ((hE.mul ((hE.const_mul 4).add_const (36*c^2))).sqrt)
  apply squeeze_zero' _ _ hbound
  · filter_upwards [unit_interval_eventually] with r hr
    exact mul_nonneg (residueEnergy_nonneg m _ hr.1.le) (squareKernel_nonneg hr.2)
  · filter_upwards [unit_interval_eventually,negative_log_one_sub.eventually_ge_atTop 1] with r hr hL
    have hk := squareKernel_nonneg hr.2
    have he0 : 0 ≤ series (errorSq A c) r :=
      tsum_nonneg (fun n ↦ mul_nonneg (sq_nonneg _) (pow_nonneg hr.1.le n))
    have hEK : 0 ≤ E r := mul_nonneg he0 hk
    have hh := mul_le_mul_of_nonneg_right (residueEnergy_bound m A hc hr.1 hr.2) hk
    rw [add_mul,sqrt_multiply_kernel _ _ _ hk] at hh
    have heq : 4*c^2*m^3/(1-r)*squareKernel r=4*c^2*m^3/(-Real.log (1-r))^2 := by
      dsimp [squareKernel]
      have ht : 1-r≠0 := (sub_pos.mpr hr.2).ne'
      field_simp
    rw [heq] at hh
    apply hh.trans
    apply add_le_add_right
    apply Real.sqrt_le_sqrt
    change E r*((4*series (errorSq A c) r+6*c^2*harmonicSqSeries r)*squareKernel r) ≤ _
    apply mul_le_mul_of_nonneg_left _ hEK
    have hmul := mul_le_mul_of_nonneg_left (harmonicSqSeries_normalized_bound hr.1 hr.2 hL)
      (by positivity : 0 ≤ 6*c^2)
    dsimp only [E]
    nlinarith

end Erdos66WitnessResidueProjection
