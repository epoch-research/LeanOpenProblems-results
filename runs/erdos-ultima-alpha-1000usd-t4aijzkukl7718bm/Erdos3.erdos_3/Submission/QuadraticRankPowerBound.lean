import Submission.PolynomialRankQuadraticInverse

/-! Elementary power bounds for the explicit spectral-symmetry rank. -/
namespace Erdos3QuadraticRankPowerBound
open Erdos3PolynomialRankSkewSymmetry Erdos3SpectralSkewSymmetry
  Erdos3BohrPowerNormalization Erdos3PolynomialRankQuadraticInverse
  Erdos3ReducedLossQuadraticInverse Erdos3UnlocalizedBilinearExtraction
set_option maxHeartbeats 6000000
set_option maxRecDepth 3000

lemma walkLength_bound {α ω t : ℝ} (ht : 1 ≤ t) (hτ : 0 < tolerance α ω)
    (hτt : 1/tolerance α ω ≤ t) : (walkLength α ω : ℝ)+1 ≤ 5*t := by
  have hh := Nat.ceil_lt_add_one (by positivity : 0 ≤ 2/tolerance α ω)
  have hh2 : 2/tolerance α ω ≤ 2*t := by
    calc
      _ = 2*(1/tolerance α ω) := by ring
      _ ≤ 2*t := by gcongr
  simp only [walkLength,Nat.cast_add,Nat.cast_one]
  linarith

lemma samplingError_inv_bound {α ω t : ℝ} (hα : 0 < α) (hω : 0 < ω)
    (ht : 1 ≤ t) (hτt : 1/tolerance α ω ≤ t) :
    1/samplingError α ω ≤ 20*t^2 := by
  have hτ := tolerance_pos hα hω
  have hw := walkLength_bound ht hτ hτt
  calc
    _ = 4*((walkLength α ω : ℝ)+1)*(1/tolerance α ω) := by unfold samplingError; simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,one_mul]
    _ ≤ 4*(5*t)*t := by gcongr
    _ = _ := by ring

lemma samplingCount_bound {α Λ ω t : ℝ} (hα : 0 < α) (hΛ : 0 < Λ) (hω : 0 < ω)
    (ht : 1 ≤ t) (hαt : 1/α ≤ t) (hΛt : 1/Λ ≤ t) (hτt : 1/tolerance α ω ≤ t) :
    (samplingCount α Λ ω : ℝ) ≤ 200000*t^9 := by
  have he := samplingError_pos hα hω
  have hit := samplingError_inv_bound hα hω ht hτt
  have hfirst : 8/(samplingError α ω)^2 ≤ 3200*t^4 := by
    calc
      _ = 8*(1/samplingError α ω)^2 := by ring
      _ ≤ 8*(20*t^2)^2 := by gcongr
      _ = _ := by ring
  have hsecond : 16/(α*(Λ/2)^4*(samplingError α ω)^2) ≤ 102400*t^9 := by
    calc
      _ = 256*(1/α)*(1/Λ)^4*(1/samplingError α ω)^2 := by ring
      _ ≤ 256*t*t^4*(20*t^2)^2 := by gcongr
      _ = _ := by ring
  have hc₁ := Nat.ceil_lt_add_one (by positivity : 0 ≤ 8/(samplingError α ω)^2)
  have hc₂ := Nat.ceil_lt_add_one (by positivity : 0 ≤ 16/(α*(Λ/2)^4*(samplingError α ω)^2))
  have hp : t^4 ≤ t^9 := pow_le_pow_right₀ ht (by decide)
  have h1 : 1 ≤ t^9 := one_le_pow₀ ht
  simp only [samplingCount,Nat.cast_add,Nat.cast_one]
  linarith

lemma rawRank_bound {α Λ ω t : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hΛ : 0 < Λ) (hω : 0 < ω)
    (ht : 1 ≤ t) (hαt : 1/α ≤ t) (hΛt : 1/Λ ≤ t) (hτt : 1/tolerance α ω ≤ t) :
    (rawRank α Λ ω : ℝ) ≤ 4000000*t^10 := by
  have hn := samplingCount_bound hα hΛ hω ht hαt hΛt hτt
  have hlog0 : 0 ≤ Real.log (1/α) := Real.log_nonneg ((le_div_iff₀ hα).mpr (by simpa using hα1))
  have hlog : Real.log (1/α) ≤ t := (Real.log_le_sub_one_of_pos (one_div_pos.mpr hα)).trans (by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by simpa only [show (2 : ℝ)-1 = 1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hf := Nat.floor_le (show 0 ≤ 16*(Real.log 2+(samplingCount α Λ ω+1 : ℕ)*Real.log (1/α)) by positivity)
  have hlin : 16*(Real.log 2+(samplingCount α Λ ω+1 : ℕ)*Real.log (1/α)) ≤ 3200032*t^10 := by
    have h1 : 1 ≤ t^9 := one_le_pow₀ ht
    have hh : (samplingCount α Λ ω+1 : ℕ) ≤ 200001*t^9 := by
      simp only [Nat.cast_add,Nat.cast_one]; linarith
    calc
      _ ≤ 16*(1+(200001*t^9)*t) := by gcongr
      _ ≤ 3200032*t^10 := by nlinarith only [one_le_pow₀ ht (n := 10)]
  have hfrac : 32/(Λ*α)^2 ≤ 32*t^4 := by
    calc
      _ = 32*(1/Λ)^2*(1/α)^2 := by ring
      _ ≤ 32*t^2*t^2 := by gcongr
      _ = _ := by ring
  have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ 32/(Λ*α)^2)
  have hp : t^4 ≤ t^10 := pow_le_pow_right₀ ht (by decide)
  have h1 : 1 ≤ t^10 := one_le_pow₀ ht
  simp only [rawRank,spectralSymmetryRank,sampleRank,Nat.cast_add,Nat.cast_one] at hf hlin ⊢
  linarith

lemma rawRadius_inv_bound {α Λ ω t : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hΛ : 0 < Λ) (hω : 0 < ω)
    (ht : 1 ≤ t) (hαt : 1/α ≤ t) (hΛt : 1/Λ ≤ t) (hτt : 1/tolerance α ω ≤ t) :
    1/rawRadius α Λ ω ≤ 5000000*t^11 := by
  have hr := rawRank_bound hα hα1 hΛ hω ht hαt hΛt hτt
  have hτ := tolerance_pos hα hω
  have hp : 1 ≤ t^10 := one_le_pow₀ ht
  have hx : ((rawRank α Λ ω : ℝ)+1)*(1/tolerance α ω) ≤ 4000001*t^11 := by
    calc
      _ ≤ (4000001*t^10)*t := by gcongr; linarith
      _ = _ := by ring
  have ht11 : 1 ≤ t^11 := one_le_pow₀ ht
  unfold rawRadius
  rcases le_total (tolerance α ω/((rawRank α Λ ω : ℝ)+1)) (1/2) with hh | hh
  · rw [min_eq_left hh]
    have he : 1/(tolerance α ω/((rawRank α Λ ω : ℝ)+1)) =
        ((rawRank α Λ ω : ℝ)+1)*(1/tolerance α ω) := by
      simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,one_mul]
    rw [he]
    linarith
  · rw [min_eq_right hh]
    norm_num
    linarith

/-- A coarse monomial estimate; t simultaneously dominates the inverse support
density, inverse skew bias, and inverse chosen tolerance. -/
theorem fixedRadiusRank_power_bound {α Λ ω t : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hΛ : 0 < Λ) (hω : 0 < ω)
    (ht : 1 ≤ t) (hαt : 1/α ≤ t) (hΛt : 1/Λ ≤ t) (hτt : 1/tolerance α ω ≤ t) :
    (fixedRadiusRank α Λ ω : ℝ) ≤ 30000000000000*t^21 := by
  have hr := rawRank_bound hα hα1 hΛ hω ht hαt hΛt hτt
  have hi := rawRadius_inv_bound hα hα1 hΛ hω ht hαt hΛt hτt
  have hc := Nat.ceil_lt_add_one (one_div_nonneg.mpr (rawRadius_pos hα hω).le : 0 ≤ 1/rawRadius α Λ ω)
  have ht11 : 1 ≤ t^11 := one_le_pow₀ ht
  have hp : (radiusPower (rawRadius α Λ ω)+1 : ℕ) ≤ 5000003*t^11 := by
    simp only [radiusPower,Nat.cast_add,Nat.cast_one]
    linarith
  calc
    _ = (radiusPower (rawRadius α Λ ω)+1 : ℝ)*(rawRank α Λ ω : ℝ) := by simp [fixedRadiusRank]
    _ ≤ (5000003*t^11)*(4000000*t^10) := mul_le_mul (by simpa only [Nat.cast_add,Nat.cast_one] using hp) hr (Nat.cast_nonneg _) (by positivity)
    _ ≤ _ := by nlinarith only [pow_nonneg (ht.trans' (by norm_num : (0 : ℝ) ≤ 1)) 21]

#print axioms fixedRadiusRank_power_bound
end Erdos3QuadraticRankPowerBound
