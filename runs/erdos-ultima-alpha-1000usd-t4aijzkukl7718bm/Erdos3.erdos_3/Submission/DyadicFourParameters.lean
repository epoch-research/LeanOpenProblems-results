import Submission.PolynomialFourDensityBound

/-! A single exponential scale uniformly bounds all density-dependent
parameters of the four-term increment at dyadic density. -/
namespace Erdos3DyadicFourParameters
open Erdos3IntegerFourDensityIncrement Erdos3IntegerFourDensityBound
  Erdos3ProgressionIncrementParameters Erdos3NormalizedQuadraticInverse
  Erdos3NormalizedQuadraticPowerBounds Erdos3SingleExponentialQuadraticInverse
open scoped Classical
set_option maxHeartbeats 3000000
set_option maxRecDepth 3000

lemma dyadic_uniformity (s : ℕ) :
    intervalUniformityThreshold ((1/2 : ℝ)^s) = (1/2 : ℝ)^(32*s+104) := by
  unfold intervalUniformityThreshold
  have h13 : (1/2 : ℝ)^13 = 1/8192 := by norm_num
  calc
    _ = (((1/2 : ℝ)^s)^4*(1/2 : ℝ)^13)^8 := by rw [h13]; ring
    _ = _ := by rw [← pow_mul,← pow_add,← pow_mul]; congr 1; omega

lemma dyadic_gain_inverse (s : ℕ) :
    1/intervalGain ((1/2 : ℝ)^s) =
      correlationDenominator*(2 : ℝ)^((32*s+104)*1988534) := by
  unfold intervalGain
  rw [dyadic_uniformity,← pow_mul,div_pow,one_pow]
  field_simp

lemma exists_dyadic_majorant (a : ℝ) : ∃ q : ℕ, a ≤ (2 : ℝ)^q := by
  obtain ⟨q,_,hq⟩ := exists_nat_pow_near (le_max_left 1 a) (by norm_num : (1 : ℝ) < 2)
  exact ⟨q+1,(le_max_right 1 a).trans hq.le⟩

lemma affine_exponent_le (q e s : ℕ) :
    q+(32*s+104)*e ≤ (q+104*e)*(s+1) := by
  nlinarith only [Nat.zero_le (q*s),Nat.zero_le (72*e*s)]

/-- The rank, gain precision, iteration count, and diagonal cutoff all fit
inside one dyadic scale with an exponent linear in log inverse density. -/
theorem dyadic_four_parameter_bound : ∃ c : ℕ, 100 ≤ c ∧ ∀ s : ℕ,
    normalizedRank (intervalUniformityThreshold ((1/2 : ℝ)^s))+1 ≤ 2^(c*(s+1)) ∧
    incrementPrecision (intervalGain ((1/2 : ℝ)^s))+2 ≤ 2^(c*(s+1)) ∧
    fourIterationCount ((1/2 : ℝ)^s) ≤ 2^(c*(s+1)) ∧
    ⌈4096/((1/2 : ℝ)^s)^4⌉₊+10 ≤ 2^(c*(s+1)) := by
  obtain ⟨q,hq⟩ := exists_dyadic_majorant (rankConstant+1)
  obtain ⟨p,hp⟩ := exists_dyadic_majorant (64*correlationDenominator+4)
  let c := max 100 (max (q+104*33407388) (p+104*1988534))
  have hc100 : 100 ≤ c := le_max_left _ _
  have hcq : q+104*33407388 ≤ c := (le_max_left _ _).trans (le_max_right _ _)
  have hcp : p+104*1988534 ≤ c := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨c,hc100,?_⟩
  intro s
  have hα : 0 < (1/2 : ℝ)^s := pow_pos (by norm_num) _
  have hδ : 0 < intervalUniformityThreshold ((1/2 : ℝ)^s) := intervalUniformityThreshold_pos hα
  have hδ1 : intervalUniformityThreshold ((1/2 : ℝ)^s) ≤ 1 := by
    rw [dyadic_uniformity]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hqexp : q+(32*s+104)*33407388 ≤ c*(s+1) :=
    (affine_exponent_le q 33407388 s).trans (Nat.mul_le_mul_right _ hcq)
  have hpexp : p+(32*s+104)*1988534 ≤ c*(s+1) :=
    (affine_exponent_le p 1988534 s).trans (Nat.mul_le_mul_right _ hcp)
  have hgain : 1/intervalGain ((1/2 : ℝ)^s) =
      correlationDenominator*(2 : ℝ)^((32*s+104)*1988534) := dyadic_gain_inverse s
  have hscale : (64/intervalGain ((1/2 : ℝ)^s)+4) ≤ (2 : ℝ)^(c*(s+1)) := by
    have hpow1 : 1 ≤ (2 : ℝ)^((32*s+104)*1988534) := one_le_pow₀ (by norm_num)
    calc
      _ = 64*(1/intervalGain ((1/2 : ℝ)^s))+4 := by ring
      _ = 64*(correlationDenominator*(2 : ℝ)^((32*s+104)*1988534))+4 := by rw [hgain]
      _ ≤ (64*correlationDenominator+4)*(2 : ℝ)^((32*s+104)*1988534) := by
        nlinarith only [hpow1]
      _ ≤ (2 : ℝ)^p*(2 : ℝ)^((32*s+104)*1988534) :=
        mul_le_mul_of_nonneg_right hp (pow_nonneg (by norm_num) _)
      _ = (2 : ℝ)^(p+(32*s+104)*1988534) := (pow_add ..).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hpexp
  constructor
  · have hR := normalizedRank_power_bound hδ hδ1
    have hδinv : 1/intervalUniformityThreshold ((1/2 : ℝ)^s) = (2 : ℝ)^(32*s+104) := by
      rw [dyadic_uniformity,div_pow,one_pow,one_div_one_div]
    rw [hδinv,← pow_mul] at hR
    have hh : (normalizedRank (intervalUniformityThreshold ((1/2 : ℝ)^s)) : ℝ)+1 ≤
        (2 : ℝ)^(c*(s+1)) := by
      have hpow1 : 1 ≤ (2 : ℝ)^((32*s+104)*33407388) := one_le_pow₀ (by norm_num)
      calc
        _ ≤ rankConstant*(2 : ℝ)^((32*s+104)*33407388)+1 := add_le_add hR le_rfl
        _ ≤ (rankConstant+1)*(2 : ℝ)^((32*s+104)*33407388) := by nlinarith only [hpow1]
        _ ≤ (2 : ℝ)^q*(2 : ℝ)^((32*s+104)*33407388) :=
          mul_le_mul_of_nonneg_right hq (pow_nonneg (by norm_num) _)
        _ = (2 : ℝ)^(q+(32*s+104)*33407388) := (pow_add ..).symm
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) hqexp
    exact_mod_cast hh
  constructor
  · have hr : 0 < intervalGain ((1/2 : ℝ)^s) := intervalGain_pos hα
    have hceil := Nat.ceil_lt_add_one (div_nonneg (by norm_num : (0 : ℝ) ≤ 64) hr.le)
    have hh : ((incrementPrecision (intervalGain ((1/2 : ℝ)^s))+2 : ℕ) : ℝ) ≤
        (2 : ℝ)^(c*(s+1)) := by
      simp only [incrementPrecision,roundedScale,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,mul_one]
      linarith only [hceil,hscale]
    exact_mod_cast hh
  constructor
  · have hr : 0 < intervalGain ((1/2 : ℝ)^s) := intervalGain_pos hα
    have hceil := Nat.ceil_lt_add_one (div_nonneg (by norm_num : (0 : ℝ) ≤ 32) hr.le)
    have hnonneg : 0 ≤ 32/intervalGain ((1/2 : ℝ)^s) := div_nonneg (by norm_num) hr.le
    have h64 : 64/intervalGain ((1/2 : ℝ)^s) = 2*(32/intervalGain ((1/2 : ℝ)^s)) := by ring
    rw [h64] at hscale
    have hh : ((fourIterationCount ((1/2 : ℝ)^s) : ℕ) : ℝ) ≤ (2 : ℝ)^(c*(s+1)) := by
      simp only [fourIterationCount,Nat.cast_add,Nat.cast_one]
      linarith only [hceil,hscale,hnonneg]
    exact_mod_cast hh
  · have he : 4096/((1/2 : ℝ)^s)^4 = (2 : ℝ)^(12+4*s) := by
      rw [← pow_mul,div_pow,one_pow,pow_add]
      have hcomm : s*4 = 4*s := Nat.mul_comm _ _
      rw [hcomm]
      norm_num
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ 4096/((1/2 : ℝ)^s)^4 by positivity)
    have hpow : 1 ≤ (2 : ℝ)^(12+4*s) := one_le_pow₀ (by norm_num)
    have hexp : 16+4*s ≤ c*(s+1) := by
      have hh := Nat.mul_le_mul_right (s+1) hc100
      nlinarith only [hh]
    have hh : ((⌈4096/((1/2 : ℝ)^s)^4⌉₊+10 : ℕ) : ℝ) ≤ (2 : ℝ)^(c*(s+1)) := by
      rw [Nat.cast_add,Nat.cast_ofNat]
      rw [he] at hceil ⊢
      calc
        _ ≤ 16*(2 : ℝ)^(12+4*s) := by linarith only [hceil,hpow]
        _ = (2 : ℝ)^(16+4*s) := by
          calc
            _ = (2 : ℝ)^4*(2 : ℝ)^(12+4*s) := by norm_num
            _ = (2 : ℝ)^(4+(12+4*s)) := (pow_add ..).symm
            _ = _ := by congr 1; omega
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) hexp
    exact_mod_cast hh

#print axioms dyadic_four_parameter_bound
end Erdos3DyadicFourParameters
