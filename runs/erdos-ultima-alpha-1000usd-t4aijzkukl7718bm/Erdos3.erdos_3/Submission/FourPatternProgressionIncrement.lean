import Submission.U3ProgressionDensityIncrement
import Submission.FourPatternPolynomialIncrement

/-! Four-pattern-free sets in prime cyclic groups have a polynomial positive
density gain on a proper progression above an explicit modulus threshold. -/
namespace Erdos3FourPatternProgressionIncrement
open Finset Erdos3U3ProgressionDensityIncrement Erdos3FourPatternPolynomialIncrement
  Erdos3ProgressionIncrementParameters Erdos3QuadraticCorrelationProgressionIncrement
  Erdos3NormalizedQuadraticInverse Erdos3NormalizedQuadraticPowerBounds
  Erdos3UniformityCounting Erdos3FiniteUniformity Erdos3FiniteFourier
  Erdos3CorrelationSifting Erdos3InteriorQuadraticDensityIncrement
open scoped BigOperators Classical
set_option maxHeartbeats 6000000
set_option maxRecDepth 3000

noncomputable def fourProgressionThreshold (α : ℝ) (L : ℕ) : ℕ :=
  incrementThreshold (normalizedRank ((α^4/8)^8)) L (fourPolynomialGain α)
noncomputable def fourProgressionStride (α : ℝ) (L : ℕ) : ℕ :=
  partitionStride (normalizedRank ((α^4/8)^8)) (incrementLinearMesh L (fourPolynomialGain α))
    (incrementCoarseMesh (normalizedRank ((α^4/8)^8)) L (fourPolynomialGain α))
    (incrementAccuracy L (fourPolynomialGain α))

lemma four_slopes_doubling (p : ℕ) [Fact p.Prime] (v : Fin 4 → ZMod p) (hv : Function.Injective v) :
    Function.Bijective (fun x : ZMod p ↦ x+x) := by
  have hp4 : 4 ≤ p := by simpa only [Fintype.card_fin,ZMod.card] using Fintype.card_le_of_injective v hv
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hh := congrArg ZMod.val h
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by rfl,ZMod.val_natCast_of_lt (by omega),ZMod.val_zero] at hh
    omega
  have hi : Function.Injective (fun x : ZMod p ↦ x+x) := by
    intro x y hxy
    apply mul_left_cancel₀ htwo
    simpa only [two_mul] using hxy
  exact ⟨hi,Finite.surjective_of_injective hi⟩

/-- The density gain is a fixed power of the original density. Unlike the
older phase-cell conclusion, the new averaging set is a proper progression. -/
theorem four_pattern_free_progression_density_increment (p : ℕ) [Fact p.Prime]
    (v : Fin 4 → ZMod p) (hv : Function.Injective v) (A : Finset (ZMod p)) (hA : A.Nonempty)
    (hsize : 4 ≤ (density A)^3*(p : ℝ))
    (hdiag : ∀ x d : ZMod p, (∀ i : Fin 4, x+v i*d ∈ A) → d = 0)
    (L : ℕ) (hL : 0 < L) (hp : fourProgressionThreshold (density A) L ≤ p) :
    ∃ a : ZMod p, ∃ d : ℕ, 0 < d ∧ d ≤ fourProgressionStride (density A) L ∧
      Function.Injective (fun j : Fin L ↦ a+j.val • (d : ZMod p)) ∧
      density A+fourPolynomialGain (density A)/16 ≤
        𝔼 j : Fin L, indicator A (a+j.val • (d : ZMod p)) := by
  have hα := density_pos A hA
  have hU := pattern_free_uniformity_lower 2 v hv A hA
    (by simpa only [ZMod.card] using hsize) hdiag
  have hU' : ((density A)^4/8)^8 ≤
      uniformityPower 2 (fun x ↦ ((indicator A x-density A : ℝ) : ℂ)) := by
    simpa only [show 2+2 = 4 from rfl,show 2^(2+1) = 8 from rfl,
      show (2 : ℝ)*(4 : ℕ) = 8 by norm_num] using hU.le
  have hδ : 0 < ((density A)^4/8)^8 := by positivity
  have hδ1 : ((density A)^4/8)^8 ≤ 1 := hU'.trans
    (uniformityPower_le_one 2 _ (fun x ↦ by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using centered_indicator_bound A x))
  have hcorr : fourPolynomialGain (density A) ≤ normalizedCorrelation (((density A)^4/8)^8) := by
    rw [← threshold_correlation_power]
    exact normalizedCorrelation_power_lower hδ hδ1
  exact U3_progression_density_increment p (four_slopes_doubling p v hv) A hδ hU'
    (fourPolynomialGain_pos hα) hcorr L hL hp

#print axioms four_pattern_free_progression_density_increment
end Erdos3FourPatternProgressionIncrement
