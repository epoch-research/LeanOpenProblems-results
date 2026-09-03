import Submission.MellinDivisorCoefficient
import Submission.GrowingCoprimeCandidates

/-! Centering the actual divisor coefficient before partial summation
extends its Mellin estimate beyond fixed compact frequency intervals.
This does not bound the full signed four-factor correlation. -/
namespace Erdos972CenteredMellinFrequencyRange

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972MellinDivisorCoefficient Erdos972MobiusPartialSums Erdos972MobiusLaplace
open Erdos972PolynomialRowScales Erdos972GrowingTypeIIReduction
open Erdos972GrowingCoprimeCandidates

set_option autoImplicit false
set_option maxHeartbeats 1500000
attribute [local irreducible] root64

/-- The constant mean is removed before applying a varying weight. -/
lemma centered_divisorCoeff_interval_prefix {U M : ℕ} (hU : 0 < U) (hUM : U ≤ M)
    (j : ℕ) :
    |(∑ n ∈ Ioc M (M+j), divisorCoeff U n)+(j : ℝ)*reciprocalMoebius U| ≤ 2*U := by
  have h₁ := divisorCoeff_prefix_error hU hUM
  have h₂ := divisorCoeff_prefix_error hU (hUM.trans (Nat.le_add_right M j))
  have he := sum_Ioc_consecutive (divisorCoeff U) (Nat.zero_le M) (Nat.le_add_right M j)
  have hh := (abs_sub ((∑ n ∈ Ioc 0 (M+j), divisorCoeff U n)+
      ((M+j : ℕ) : ℝ)*reciprocalMoebius U-1)
    ((∑ n ∈ Ioc 0 M, divisorCoeff U n)+(M : ℝ)*reciprocalMoebius U-1)).trans
      (add_le_add h₂ h₁)
  rw [← he] at hh
  push_cast at hh
  have hid : (∑ n ∈ Ioc 0 M, divisorCoeff U n)+
      (∑ n ∈ Ioc M (M+j), divisorCoeff U n)+
      ((M : ℝ)+j)*reciprocalMoebius U-1-
      ((∑ n ∈ Ioc 0 M, divisorCoeff U n)+(M : ℝ)*reciprocalMoebius U-1) =
      (∑ n ∈ Ioc M (M+j), divisorCoeff U n)+(j : ℝ)*reciprocalMoebius U := by ring
  rw [hid] at hh
  linarith only [hh]

lemma centered_divisorCoeff_mellin_bound (t : ℝ) {U M : ℕ}
    (hU : 0 < U) (hUM : U ≤ M) :
    ‖∑ n ∈ Ioc M (2*M), mellinPhase t n*
      ((divisorCoeff U n+reciprocalMoebius U : ℝ) : ℂ)‖ ≤ 2*U*(1+|t|) := by
  have hM : 0 < M := hU.trans_le hUM
  let w : ℕ → ℂ := fun n => mellinPhase t (M+n+1 : ℕ)
  let z : ℕ → ℂ := fun n => ((divisorCoeff U (M+n+1)+reciprocalMoebius U : ℝ) : ℂ)
  have hp (j : ℕ) (_hj : j ≤ M) : ‖∑ n ∈ range j, z n‖ ≤ 2*U := by
    dsimp only [z]
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs, sum_add_distrib,
      sum_shift_eq_Ioc]
    simp only [sum_const, card_range, nsmul_eq_mul]
    exact centered_divisorCoeff_interval_prefix hU hUM j
  have hh := norm_weighted_prefix w z M (2*U) 1 |t| hp
    (by dsimp only [w]; rw [norm_mellinPhase]) (mellinPhase_variation t hM)
  dsimp only [w, z] at hh
  rw [sum_shift_eq_Ioc (fun n => mellinPhase t n*
    ((divisorCoeff U n+reciprocalMoebius U : ℝ) : ℂ)) M M] at hh
  simpa only [show M+M = 2*M by omega, mul_comm] using hh

lemma unweighted_mellin_sum_bound (t : ℝ) (M : ℕ) :
    ‖∑ n ∈ Ioc M (2*M), mellinPhase t n‖ ≤ (M : ℝ) := by
  apply (norm_sum_le _ _).trans
  simp only [norm_mellinPhase, sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
  norm_cast
  omega

/-- Unlike the older bound, the reciprocal Möbius mean is NOT multiplied
by 1+|t|. No quantitative Mertens rate is used. -/
theorem divisorCoeff_mellin_centered_bound (t : ℝ) {U M : ℕ}
    (hU : 0 < U) (hUM : U ≤ M) :
    ‖∑ n ∈ Ioc M (2*M), mellinPhase t n*(divisorCoeff U n : ℂ)‖ ≤
      |reciprocalMoebius U| *(M : ℝ)+2*U*(1+|t|) := by
  have hc := centered_divisorCoeff_mellin_bound t hU hUM
  have he : (∑ n ∈ Ioc M (2*M), mellinPhase t n*(divisorCoeff U n : ℂ)) =
      (∑ n ∈ Ioc M (2*M), mellinPhase t n*
        ((divisorCoeff U n+reciprocalMoebius U : ℝ) : ℂ))-
      (reciprocalMoebius U : ℂ)*(∑ n ∈ Ioc M (2*M), mellinPhase t n) := by
    simp only [Complex.ofReal_add, mul_add, sum_add_distrib, ← sum_mul]
    ring
  rw [he]
  apply (norm_sub_le _ _).trans
  have hb : ‖(reciprocalMoebius U : ℂ)*(∑ n ∈ Ioc M (2*M), mellinPhase t n)‖ ≤
      |reciprocalMoebius U| *(M : ℝ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (unweighted_mellin_sum_bound t M) (abs_nonneg _)
  linarith only [hc, hb]

/-- A growing range: |t|<=M/U². Only U->infinity and U/M->0 are needed.
The ratio M/U² is not assumed to be of floor-strip bandwidth. -/
theorem divisorCoeff_mellin_growing_uniform (U M : ℕ → ℕ)
    (hU : Tendsto U atTop atTop) (hUM : ∀ᶠ k : ℕ in atTop, U k ≤ M k)
    (hratio : Tendsto (fun k => (U k : ℝ)/(M k : ℝ)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ t : ℝ, |t| ≤ (M k : ℝ)/(U k : ℝ)^2 →
      ‖∑ n ∈ Ioc (M k) (2*M k), mellinPhase t n*(divisorCoeff (U k) n : ℂ)‖ ≤
        ε*(M k : ℝ) := by
  have hs : Tendsto (fun k => |reciprocalMoebius (U k)|) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, abs_zero] using (reciprocalMoebius_tendsto_zero.comp hU).abs
  have hi : Tendsto (fun k => 1/(U k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hU)
  have hb := (hs.add (hratio.const_mul 2)).add (hi.const_mul 2)
  simp only [mul_zero, add_zero] at hb
  filter_upwards [(tendsto_order.mp hb).2 ε hε, hUM, hU.eventually_ge_atTop 1]
    with k hk hUMk hUk
  intro t ht
  have hUR : (0 : ℝ) < U k := Nat.cast_pos.mpr hUk
  have hMR : (0 : ℝ) < M k := Nat.cast_pos.mpr (hUk.trans hUMk)
  have hfreq := mul_le_mul_of_nonneg_left (add_le_add_left ht 1)
    (show 0 ≤ 2*(U k : ℝ) by positivity)
  have he : (|reciprocalMoebius (U k)|+2*((U k : ℝ)/(M k : ℝ))+2*(1/(U k : ℝ)))*
      (M k : ℝ) = |reciprocalMoebius (U k)| *(M k : ℝ)+
        2*(U k : ℝ)*(1+(M k : ℝ)/(U k : ℝ)^2) := by
    field_simp
    ring
  have hbudget := mul_le_mul_of_nonneg_right hk.le hMR.le
  rw [he] at hbudget
  have hbase := divisorCoeff_mellin_centered_bound t hUk hUMk
  linarith only [hbase, hfreq, hbudget]

lemma balanced_cutoff_ratio_tendsto :
    Tendsto (fun u : ℕ => (growingCutoff u : ℝ)/(u^3 : ℕ)) atTop (𝓝 0) := by
  have hi : Tendsto (fun u : ℕ => 1/(u : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall (fun u => by positivity)) _ hi
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with u hu
  have huR : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hWU : growingCutoff u ≤ u := (growingCutoff_eligible u).1.trans (root64_le_self u)
  have hW : (growingCutoff u : ℝ) ≤ (u : ℝ)^2 := by
    have hh := hWU.trans (Nat.le_self_pow (by decide : 2 ≠ 0) u)
    exact_mod_cast hh
  push_cast
  apply (div_le_div_of_nonneg_right hW (by positivity : 0 ≤ (u : ℝ)^3)).trans_eq
  field_simp

noncomputable def balancedMellinRange (u : ℕ) : ℝ :=
  (u : ℝ)^3/(growingCutoff u : ℝ)^2

/-- The new actual-coefficient frequency range grows at least as u² on
balanced blocks M=u³ at the direct scale N=u⁶. -/
lemma balancedMellinRange_tendsto : Tendsto balancedMellinRange atTop atTop := by
  have hu := (tendsto_pow_atTop (α := ℝ) (by decide : 2 ≠ 0)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply tendsto_atTop_mono' atTop _ hu
  filter_upwards [eventually_ge_atTop (1 : ℕ), growingCutoff_tendsto.eventually_ge_atTop 1]
    with u hu hW
  have hWR : (0 : ℝ) < growingCutoff u := Nat.cast_pos.mpr hW
  have hbound : (growingCutoff u : ℝ)^2 ≤ u := by
    have hh := (growingCutoff_eligible u).2.trans (root64_le_self u)
    simpa only [pow_two, Nat.cast_mul] using (Nat.cast_le.mpr hh : (growingCutoff u*growingCutoff u : ℕ) ≤ (u : ℝ))
  unfold balancedMellinRange
  apply (le_div_iff₀ (sq_pos_of_pos hWR)).mpr
  have hh := mul_le_mul_of_nonneg_left hbound (sq_nonneg (u : ℝ))
  dsimp only [Function.comp_def]
  nlinarith only [hh]

/-- Uniform cancellation over this genuinely growing range, for the
actual Vaughan divisor coefficient at the balanced growing cutoff. -/
theorem eventually_balanced_mellin_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, ∀ t : ℝ, |t| ≤ balancedMellinRange u →
      ‖∑ n ∈ Ioc (u^3) (2*u^3),
        mellinPhase t n*(divisorCoeff (growingCutoff u) n : ℂ)‖ ≤ ε*(u : ℝ)^3 := by
  have hh := divisorCoeff_mellin_growing_uniform growingCutoff (fun u => u^3)
    growingCutoff_tendsto (Eventually.of_forall (fun u =>
      ((growingCutoff_eligible u).1.trans (root64_le_self u)).trans
        (Nat.le_self_pow (by decide) u))) balanced_cutoff_ratio_tendsto hε
  simpa only [Nat.cast_pow, balancedMellinRange] using hh


/-- The enlarged range is still sublinear even in the balanced factor
length M=u³, and hence does not reach the bandwidth N=u⁶. -/
lemma balancedMellinRange_div_factor_tendsto_zero :
    Tendsto (fun u : ℕ => balancedMellinRange u/(u : ℝ)^3) atTop (𝓝 0) := by
  have hpow := (tendsto_pow_atTop (α := ℝ) (by decide : 2 ≠ 0)).comp
    (tendsto_natCast_atTop_atTop.comp growingCutoff_tendsto)
  have hi : Tendsto (fun u : ℕ => 1/(growingCutoff u : ℝ)^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hpow
  apply hi.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ), growingCutoff_tendsto.eventually_ge_atTop 1]
    with u hu hW
  have huR : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hWR : (0 : ℝ) < growingCutoff u := Nat.cast_pos.mpr hW
  unfold balancedMellinRange
  field_simp

lemma balancedMellinRange_div_cutoff_tendsto_zero :
    Tendsto (fun u : ℕ => balancedMellinRange u/(u : ℝ)^6) atTop (𝓝 0) := by
  have hi : Tendsto (fun u : ℕ => 1/(u : ℝ)^3) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (α := ℝ) (by decide : 3 ≠ 0)).comp
      tendsto_natCast_atTop_atTop)
  have hh := balancedMellinRange_div_factor_tendsto_zero.mul hi
  simpa only [mul_zero, div_mul_div_comm, mul_one, ← pow_add,
    show 3+3 = 6 by rfl] using hh

#print axioms divisorCoeff_mellin_centered_bound
#print axioms divisorCoeff_mellin_growing_uniform
#print axioms balancedMellinRange_tendsto
#print axioms eventually_balanced_mellin_small
end Erdos972CenteredMellinFrequencyRange
