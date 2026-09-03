import Submission.IntervalProgressionRectification
import Submission.FourPatternProgressionIncrement

/-! An iteratable four-term density increment for integer intervals. The
reference density is preserved through cyclic embedding and rectification. -/
namespace Erdos3IntegerFourDensityIncrement
open Finset Erdos3IntervalProgressionRectification Erdos3IntervalFourUniformity
  Erdos3CyclicIntervalMask Erdos3U3ProgressionSpan Erdos3FourPatternProgressionIncrement
  Erdos3ProgressionIncrementParameters Erdos3NormalizedQuadraticInverse
  Erdos3NormalizedQuadraticPowerBounds Erdos3FiniteUniformity Erdos3CorrelationSifting
open scoped BigOperators Classical
set_option maxHeartbeats 6000000
set_option maxRecDepth 3000

noncomputable def intervalUniformityThreshold (α : ℝ) : ℝ := (α^4/8192)^8
noncomputable def intervalGain (α : ℝ) : ℝ := (intervalUniformityThreshold α)^1988534/correlationDenominator
noncomputable def requestedCyclicLength (α : ℝ) (ℓ : ℕ) : ℕ := roundedScale (ℓ : ℝ) (intervalGain α)
noncomputable def intervalStepThreshold (α : ℝ) (ℓ : ℕ) : ℕ :=
  max 8 (max ⌈4096/α^4⌉₊ (incrementThreshold (normalizedRank (intervalUniformityThreshold α))
    (requestedCyclicLength α ℓ) (intervalGain α)))

lemma intervalUniformityThreshold_pos {α : ℝ} (hα : 0 < α) : 0 < intervalUniformityThreshold α := by
  unfold intervalUniformityThreshold
  positivity
lemma intervalGain_pos {α : ℝ} (hα : 0 < α) : 0 < intervalGain α :=
  div_pos (pow_pos (intervalUniformityThreshold_pos hα) _) correlationDenominator_pos

/-- Uniform gain at every stage with density at least alpha. For any requested
next interval length ell, the explicit threshold ensures a new four-term-free
interval of length at least ell and a gain intervalGain(alpha)/32 over the
ACTUAL old density. Thus no fixed density dilution occurs. -/
theorem integer_four_density_increment {α : ℝ} (hα : 0 < α)
    (N ℓ : ℕ) (hbig : intervalStepThreshold α ℓ ≤ N)
    (S : Finset ℕ) (hS : S ⊆ range N) (hfree : (S : Set ℕ).IsAPOfLengthFree 4)
    (hdensity : α ≤ intervalDensity S N) :
    ∃ m : ℕ, ∃ T : Finset ℕ, 0 < m ∧ ℓ ≤ m ∧ m ≤ N ∧ T ⊆ range m ∧
      (T : Set ℕ).IsAPOfLengthFree 4 ∧
      intervalDensity S N+intervalGain α/32 ≤ intervalDensity T m := by
  have hN8 : 8 ≤ N := (le_max_left _ _).trans hbig
  have hceil : ⌈4096/α^4⌉₊ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hbig)
  have hthreshold : incrementThreshold (normalizedRank (intervalUniformityThreshold α))
      (requestedCyclicLength α ℓ) (intervalGain α) ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hbig)
  have hN : 0 < N := by omega
  obtain ⟨p,hprime,hNp,hpN⟩ := Nat.exists_prime_lt_and_le_two_mul (2*N) (by omega)
  letI : Fact p.Prime := ⟨hprime⟩
  have hNp' : N ≤ p := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hβ : 0 < intervalDensity S N := hα.trans_le hdensity
  have hSne : S.Nonempty := by
    have hs : (0 : ℝ) < S.card := by
      have hh := (lt_div_iff₀ hN').mp hβ
      simpa only [zero_mul] using hh
    exact card_pos.mp (by exact_mod_cast hs)
  have hsize : 4096 ≤ α^4*(p : ℝ) := by
    have hh : 4096/α^4 ≤ (p : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (hceil.trans hNp'))
    have hh' := (div_le_iff₀ (pow_pos hα 4)).mp hh
    simpa only [mul_comm] using hh'
  have hpow : α^4 ≤ (intervalDensity S N)^4 := pow_le_pow_left₀ hα.le hdensity 4
  have hsize' : 4096 ≤ (intervalDensity S N)^4*(p : ℝ) :=
    hsize.trans (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _))
  have hUbig := interval_four_uniformity_lower p N hN8 hNp.le (by omega) S hS hSne hfree hsize'
  have hU : intervalUniformityThreshold α ≤ uniformityPower 2 (fun x ↦ ((relativeBalance p N S x : ℝ) : ℂ)) := by
    apply le_trans _ hUbig.le
    exact pow_le_pow_left₀ (by positivity : 0 ≤ α^4/8192)
      (div_le_div_of_nonneg_right hpow (by norm_num)) 8
  have hf := relativeBalance_bound p N hN S hS
  have hδ := intervalUniformityThreshold_pos hα
  have hδ1 : intervalUniformityThreshold α ≤ 1 := hU.trans
    (uniformityPower_le_one 2 _ (fun x ↦ by simpa only [Complex.norm_real,Real.norm_eq_abs] using hf x))
  have hr := intervalGain_pos hα
  have hcorr : intervalGain α ≤ normalizedCorrelation (intervalUniformityThreshold α) :=
    normalizedCorrelation_power_lower hδ hδ1
  have hL : 0 < requestedCyclicLength α ℓ := roundedScale_pos _ _
  have h2 := four_slopes_doubling p (fun i : Fin 4 ↦ (i.val : ZMod p)) (four_slopes_injective p (by omega))
  obtain ⟨a,d,hd,_,hspan,_,hmean⟩ := U3_progression_increment_with_span p h2 (relativeBalance p N S)
    hf (relativeBalance_mean_zero p N hN hNp' S hS) hδ hU hr hcorr
    (requestedCyclicLength α ℓ) hL (hthreshold.trans hNp')
  obtain ⟨b,m,hm,hsizeM,hinside,hinc⟩ := interval_progression_rectification p N hN hNp' S hS a d
    (requestedCyclicLength α ℓ) hd hL hspan (by positivity : 0 < intervalGain α/16) hmean
  have hℓ : ℓ ≤ m := by
    have hL' : (0 : ℝ) < requestedCyclicLength α ℓ := by exact_mod_cast hL
    have hh := (div_le_iff₀ hL').mp (roundedScale_ratio (ℓ : ℝ) hr)
    have hm' : (ℓ : ℝ) ≤ m := by linarith only [hh,hsizeM]
    exact_mod_cast hm'
  have hmN : m ≤ N := by
    have hh := hinside (m-1) (by omega)
    have hd' : m-1 ≤ (m-1)*d := by simpa using Nat.mul_le_mul_left (m-1) hd
    omega
  refine ⟨m,progressionTrace S b d m,hm,hℓ,hmN,progressionTrace_subset S b d m,
    progressionTrace_free S (by decide) hfree b d m hd,?_⟩
  simpa only [div_div,show (16 : ℝ)*2 = 32 by norm_num] using hinc

#print axioms integer_four_density_increment
end Erdos3IntegerFourDensityIncrement
