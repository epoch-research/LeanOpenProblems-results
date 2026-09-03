import Submission.CenteredMellinFrequencyRange
import Submission.MellinMeanSquare
import Submission.SquarefreePrimeOutputMean

/-! A finite low-frequency four-factor bound with the centered ACTUAL
Vaughan divisor coefficients and the ACTUAL truncated Mangoldt factors.
This is not a representation or a bound for the full floor-strip sum. -/
namespace Erdos972CenteredLowMellinBlock

open Finset Filter MeasureTheory ArithmeticFunction
open scoped Topology ComplexConjugate
open Erdos972MellinDivisorCoefficient Erdos972CenteredMellinFrequencyRange
open Erdos972MellinMeanSquare Erdos972Vaughan Erdos972ChebyshevRowMean
open Erdos972MobiusPartialSums Erdos972SquarefreePrimeOutputMean
open Erdos972GrowingTypeIIReduction Erdos972GrowingCoprimeCandidates

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def centeredBlock (U M : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Ioc M (2*M), mellinPhase t n*
    ((divisorCoeff U n+reciprocalMoebius U : ℝ) : ℂ)

noncomputable def mangoldtBlock (V M : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Ioc M (2*M), ((tail vonMangoldt V n : ℝ) : ℂ)*mellinPhase t n

lemma continuous_mangoldtBlock (V M : ℕ) : Continuous (mangoldtBlock V M) := by
  unfold mangoldtBlock
  apply continuous_finset_sum
  intro n hn
  unfold mellinPhase
  fun_prop

lemma mangoldtBlock_energy_le (V M : ℕ) :
    energy (Ioc M (2*M)) (fun n => ((tail vonMangoldt V n : ℝ) : ℂ)) ≤
      Real.log (2*M : ℕ)*Chebyshev.psi (2*M : ℕ) := by
  apply le_trans _ (vonMangoldt_energy (Ioc M (2*M)) (Ioc_subset_Ioc (Nat.zero_le M) le_rfl))
  unfold energy
  apply sum_le_sum
  intro n hn
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tail_vonMangoldt_nonneg V n), abs_of_nonneg vonMangoldt_nonneg]
  exact pow_le_pow_left₀ (tail_vonMangoldt_nonneg V n) (tail_vonMangoldt_le V n) 2

/-- A uniform energy estimate retaining both Mangoldt weights. -/
lemma mangoldtBlock_mean_square_le (V M : ℕ) {H : ℝ} (hH : 0 ≤ H) (hHM : H ≤ M) :
    (∫ t in -H..H, ‖mangoldtBlock V M t‖^2) ≤
      140*(M : ℝ)^2*(1+Real.log (2*M : ℕ))^2 := by
  have hh := mellin_mean_square (Ioc M (2*M))
    (Ioc_subset_Ioc (Nat.zero_le M) le_rfl)
    (fun n => ((tail vonMangoldt V n : ℝ) : ℂ)) (-H) H
  have he := mangoldtBlock_energy_le V M
  have hL : 0 ≤ Real.log (2*M : ℕ) := Real.log_natCast_nonneg _
  have hC : 0 ≤ 2*H+8*(M : ℝ)*(1+Real.log (2*M : ℕ)) := by positivity
  have hpsi : Chebyshev.psi (2*M : ℕ) ≤ 14*(M : ℝ) := by
    convert psi_le_seven_mul (Nat.cast_nonneg (2*M)) using 1
    push_cast
    ring
  have hE : energy (Ioc M (2*M)) (fun n => ((tail vonMangoldt V n : ℝ) : ℂ)) ≤
      14*(M : ℝ)*(1+Real.log (2*M : ℕ)) := by
    have hm := mul_le_mul_of_nonneg_left hpsi hL
    nlinarith only [he, hm, Nat.cast_nonneg (α := ℝ) M]
  have hc : 2*H+8*(M : ℝ)*(1+Real.log (2*M : ℕ)) ≤
      10*(M : ℝ)*(1+Real.log (2*M : ℕ)) := by
    nlinarith only [hHM, mul_nonneg (Nat.cast_nonneg (α := ℝ) M) hL]
  have hi := (abs_le.mp hh).2
  have hmain : (∫ t in -H..H, ‖mangoldtBlock V M t‖^2) ≤
      (2*H+8*(M : ℝ)*(1+Real.log (2*M : ℕ)))*
        energy (Ioc M (2*M)) (fun n => ((tail vonMangoldt V n : ℝ) : ℂ)) := by
    dsimp only [mangoldtBlock]
    push_cast at hi ⊢
    linarith only [hi]
  apply hmain.trans
  have hm := mul_le_mul hc hE (energy_nonneg _ _) (by positivity :
    0 ≤ 10*(M : ℝ)*(1+Real.log (2*M : ℕ)))
  nlinarith only [hm]

lemma centeredBlock_low_bound {U M : ℕ} (hU : 0 < U) (hUM : U^2 ≤ M)
    {t : ℝ} (ht : |t| ≤ (M : ℝ)/(U : ℝ)^2) :
    ‖centeredBlock U M t‖ ≤ 4*(M : ℝ)/(U : ℝ) := by
  have hUM' : U ≤ M := (Nat.le_self_pow (by decide : 2 ≠ 0) U).trans hUM
  have hh := centered_divisorCoeff_mellin_bound t hU hUM'
  have hUR : (0 : ℝ) < U := Nat.cast_pos.mpr hU
  have hsq : (U : ℝ)^2 ≤ M := by exact_mod_cast hUM
  have hdiv : (U : ℝ) ≤ (M : ℝ)/U := (le_div_iff₀ hUR).mpr (by nlinarith only [hsq])
  have hf := mul_le_mul_of_nonneg_left (add_le_add_left ht 1)
    (show 0 ≤ 2*(U : ℝ) by positivity)
  have he : 2*(U : ℝ)*(1+(M : ℝ)/(U : ℝ)^2) = 2*(U : ℝ)+2*(M : ℝ)/U := by
    field_simp
  dsimp only [centeredBlock]
  rw [add_comm (|t|) 1, add_comm ((M : ℝ)/(U : ℝ)^2) 1] at hf
  rw [he] at hf
  apply (hh.trans hf).trans
  ring_nf at hdiv ⊢
  linarith only [hdiv]

noncomputable def lowMellinFourFactor (U V S T M : ℕ) (H : ℝ) (K : ℝ → ℂ) : ℂ :=
  ∫ t in -H..H, K t*(centeredBlock U M t*mangoldtBlock V M t)*
    conj (centeredBlock S M t*mangoldtBlock T M t)

/-- A bound for an explicitly defined low-frequency integral. No claim
that the higher-frequency floor-strip contribution is small is made. -/
theorem lowMellinFourFactor_bound {U S M : ℕ} (hU : 0 < U) (hS : 0 < S)
    (hUM : U^2 ≤ M) (hSM : S^2 ≤ M) (V T : ℕ) {H : ℝ} (hH : 0 ≤ H)
    (hHU : H ≤ (M : ℝ)/(U : ℝ)^2) (hHS : H ≤ (M : ℝ)/(S : ℝ)^2)
    (K : ℝ → ℂ) (hK : ∀ t : ℝ, |t| ≤ H → ‖K t‖ ≤ 1/(M : ℝ)^2) :
    ‖lowMellinFourFactor U V S T M H K‖ ≤
      2240*(M : ℝ)^2*(1+Real.log (2*M : ℕ))^2/((U : ℝ)*S) := by
  have hUR : (0 : ℝ) < U := Nat.cast_pos.mpr hU
  have hSR : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr ((Nat.pow_pos hU).trans_le hUM)
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hHM : H ≤ M := hHU.trans (div_le_self (Nat.cast_nonneg M) (by nlinarith only [hU1]))
  let C : ℝ := 16/((U : ℝ)*S)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp (t : ℝ) (ht : |t| ≤ H) :
      ‖K t*(centeredBlock U M t*mangoldtBlock V M t)*
        conj (centeredBlock S M t*mangoldtBlock T M t)‖ ≤
      (C/2)*(‖mangoldtBlock V M t‖^2+‖mangoldtBlock T M t‖^2) := by
    have ha := centeredBlock_low_bound hU hUM (ht.trans hHU)
    have hc := centeredBlock_low_bound hS hSM (ht.trans hHS)
    have hweight : ‖K t‖*‖centeredBlock U M t‖*‖centeredBlock S M t‖ ≤ C := by
      calc
        _ ≤ (1/(M : ℝ)^2)*(4*(M : ℝ)/U)*(4*(M : ℝ)/S) := by
          exact mul_le_mul (mul_le_mul (hK t ht) ha (norm_nonneg _) (by positivity)) hc
            (norm_nonneg _) (by positivity)
        _ = _ := by dsimp [C]; field_simp; ring
    have hprod : ‖mangoldtBlock V M t‖*‖mangoldtBlock T M t‖ ≤
        (‖mangoldtBlock V M t‖^2+‖mangoldtBlock T M t‖^2)/2 := by
      nlinarith only [sq_nonneg (‖mangoldtBlock V M t‖-‖mangoldtBlock T M t‖)]
    have hm := mul_le_mul hweight hprod
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hC
    simp only [norm_mul, Complex.norm_conj]
    nlinarith only [hm]
  have hbound : IntervalIntegrable (fun t =>
      (C/2)*(‖mangoldtBlock V M t‖^2+‖mangoldtBlock T M t‖^2)) volume (-H) H := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (((continuous_mangoldtBlock V M).norm.pow 2).add
      ((continuous_mangoldtBlock T M).norm.pow 2))
  have hi := intervalIntegral.norm_integral_le_of_norm_le (show -H ≤ H by linarith)
    (Eventually.of_forall (fun t (ht : t ∈ Set.Ioc (-H) H) =>
      hp t (abs_le.mpr ⟨ht.1.le, ht.2⟩))) hbound
  have hV := mangoldtBlock_mean_square_le V M hH hHM
  have hT := mangoldtBlock_mean_square_le T M hH hHM
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    (((continuous_mangoldtBlock V M).norm.pow 2).intervalIntegrable _ _)
    (((continuous_mangoldtBlock T M).norm.pow 2).intervalIntegrable _ _)] at hi
  apply hi.trans
  have hh := mul_le_mul_of_nonneg_left (add_le_add hV hT) (show 0 ≤ C/2 from div_nonneg hC (by norm_num))
  dsimp only [C] at hh ⊢
  convert hh using 1
  ring


lemma balanced_block_log_bound {u : ℕ} (hu : 0 < u) :
    1+Real.log (2*u^3 : ℕ) ≤ 4*(1+Real.log u) := by
  have huR : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hlog := Real.log_natCast_nonneg u
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    simpa only [show (2 : ℝ)-1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero 3 huR.ne'), Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [htwo, hlog]

noncomputable def balancedLowMellinBudget (u : ℕ) : ℝ :=
  35840*((1+Real.log u)/(growingCutoff u : ℝ))^2

lemma balancedLowMellinBudget_tendsto : Tendsto balancedLowMellinBudget atTop (𝓝 0) := by
  have hh := ((growingCutoff_log_div_tendsto 1 (by norm_num) 1).pow 2).const_mul 35840
  unfold balancedLowMellinBudget
  simpa only [pow_one, one_mul, zero_pow (by decide : 2 ≠ 0), mul_zero] using hh

/-- The normalized low-frequency budget tends to zero with an explicit
power-root saving, without requiring a logarithmic Mertens rate. -/
lemma balanced_lowMellin_bound {u : ℕ} (hu : 0 < u) (hW : 0 < growingCutoff u)
    (V T : ℕ) {H : ℝ} (hH : 0 ≤ H) (hHr : H ≤ balancedMellinRange u)
    (K : ℝ → ℂ) (hK : ∀ t : ℝ, |t| ≤ H → ‖K t‖ ≤ 1/(u : ℝ)^6) :
    ‖lowMellinFourFactor (growingCutoff u) V (growingCutoff u) T (u^3) H K‖ ≤
      balancedLowMellinBudget u*(u : ℝ)^6 := by
  have hWU : (growingCutoff u)^2 ≤ u := by
    simpa only [pow_two] using (growingCutoff_eligible u).2.trans (root64_le_self u)
  have hWM : (growingCutoff u)^2 ≤ u^3 := hWU.trans (Nat.le_self_pow (by decide) u)
  have hHr' : H ≤ ((u^3 : ℕ) : ℝ)/(growingCutoff u : ℝ)^2 := by
    simpa only [balancedMellinRange, Nat.cast_pow] using hHr
  have hK' (t : ℝ) (ht : |t| ≤ H) : ‖K t‖ ≤ 1/(((u^3 : ℕ) : ℝ)^2) := by
    convert hK t ht using 1
    push_cast
    ring
  have hf := lowMellinFourFactor_bound hW hW hWM hWM V T hH hHr' hHr' K hK'
  have he : (((u^3 : ℕ) : ℝ)^2) = (u : ℝ)^6 := by push_cast; ring
  rw [he] at hf
  have hlog := balanced_block_log_bound hu
  calc
    _ ≤ 2240*(u : ℝ)^6*(1+Real.log (2*u^3 : ℕ))^2/
        ((growingCutoff u : ℝ)*growingCutoff u) := hf
    _ ≤ 2240*(u : ℝ)^6*(4*(1+Real.log u))^2/
        ((growingCutoff u : ℝ)*growingCutoff u) := by
      gcongr
    _ = _ := by unfold balancedLowMellinBudget; ring

/-- Every sufficiently large scale has a small low-frequency integral,
SIMULTANEOUSLY for both Mangoldt cutoffs, all shorter frequency intervals,
and every kernel obeying the displayed norm bound. -/
theorem eventually_balanced_lowMellin_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, ∀ V T : ℕ, ∀ H : ℝ, 0 ≤ H → H ≤ balancedMellinRange u →
      ∀ K : ℝ → ℂ, (∀ t : ℝ, |t| ≤ H → ‖K t‖ ≤ 1/(u : ℝ)^6) →
        ‖lowMellinFourFactor (growingCutoff u) V (growingCutoff u) T (u^3) H K‖ ≤
          ε*(u : ℝ)^6 := by
  filter_upwards [(tendsto_order.mp balancedLowMellinBudget_tendsto).2 ε hε,
    eventually_ge_atTop (1 : ℕ), growingCutoff_tendsto.eventually_ge_atTop 1]
    with u hb hu hW
  intro V T H hH hHr K hK
  exact (balanced_lowMellin_bound hu hW V T hH hHr K hK).trans
    (mul_le_mul_of_nonneg_right hb.le (by positivity))

#print axioms balancedLowMellinBudget_tendsto
#print axioms eventually_balanced_lowMellin_small

#print axioms mangoldtBlock_mean_square_le
#print axioms centeredBlock_low_bound
#print axioms lowMellinFourFactor_bound
end Erdos972CenteredLowMellinBlock
