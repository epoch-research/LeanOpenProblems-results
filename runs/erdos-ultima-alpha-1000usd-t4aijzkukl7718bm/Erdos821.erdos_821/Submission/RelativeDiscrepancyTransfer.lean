import Submission.MomentSmoothTransfer
import Submission.BinomialMangoldtLower

/-!
# Conditional transfer from full-range relative progression discrepancy

The relative discrepancy hypothesis in this file is NOT proved. The results
identify a sufficient analytic input; they do not settle Erdős 821.
-/

open Nat Filter ArithmeticFunction Asymptotics
open scoped Classical BigOperators Topology

namespace Erdos821.HigherDivisors

open AnalyticSieve

/-- Prime powers of exponent at least two are negligible at every fixed order. -/
theorem eventually_nonprimeMangoldtMoment_le_linear (k : ℕ) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop, nonprimeMangoldtMoment (k+1) X ≤ c*(X : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := nonprimeMangoldtMoment_subpower_bound k
  have hC0 : 0 < C := by linarith
  have ho : (fun X : ℕ => Real.log (X : ℝ)) =o[atTop]
      (fun X : ℕ => (X : ℝ)^(1/4 : ℝ)) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/4)).comp_tendsto
      tendsto_natCast_atTop_atTop
  filter_upwards [ho.bound (show 0 < c/(2*C) from div_pos hc (by positivity)),
    eventually_ge_atTop 1] with X hlog hX
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hlog0 : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  simp only [Real.norm_eq_abs, abs_of_nonneg hlog0,
    abs_of_nonneg (Real.rpow_nonneg hX0.le _)] at hlog
  calc
    nonprimeMangoldtMoment (k+1) X ≤ 2*C*(X : ℝ)^(3/4 : ℝ)*Real.log X := hbound X hX
    _ ≤ 2*C*(X : ℝ)^(3/4 : ℝ)*(c/(2*C)*(X : ℝ)^(1/4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = c*(X : ℝ) := by
      have he : (X : ℝ)^(3/4 : ℝ)*(X : ℝ)^(1/4 : ℝ) = (X : ℝ) := by
        rw [← Real.rpow_add hX0]
        norm_num
      calc
        _ = c*((X : ℝ)^(3/4 : ℝ)*(X : ℝ)^(1/4 : ℝ)) := by field_simp
        _ = _ := by rw [he]

lemma tendsto_momentScale_exponent (t : ℕ) (ht : 1 ≤ t) :
    Tendsto (fun L : ℕ => 128*t*L) atTop atTop := by
  apply tendsto_atTop_mono (fun L => ?_) tendsto_id
  exact Nat.le_mul_of_pos_left L (by positivity)

lemma tendsto_momentScaleX (t : ℕ) (ht : 1 ≤ t) :
    Tendsto (momentScaleX t) atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))).comp
    (tendsto_momentScale_exponent t ht)

lemma eventually_momentScale_mangoldt_five_eighths (t : ℕ) (ht : 1 ≤ t) :
    ∀ᶠ L : ℕ in atTop,
      (5/8 : ℝ)*(momentScaleX t L : ℝ) ≤ mangoldtSum (momentScaleX t L) :=
  (tendsto_momentScale_exponent t ht).eventually eventually_dyadic_mangoldt_five_eighths

/-- The unevaluated arithmetic obligation. It concerns the full modulus
range Q=X. Both the divisor order and the root parameter are fixed before
letting L tend to infinity. -/
def RelativeFullRangeDiscrepancy : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∀ t : ℕ, 2 ≤ t →
    (fun L : ℕ => divisorProgressionError r (momentScaleX t L) (momentScaleX t L))
      =o[atTop] (fun L : ℕ =>
        (momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^r)

/-- A finite comparison retaining the factorial coefficient. The two error
bounds here must be supplied, not inferred from the main term. -/
lemma shiftedPrimeMoment_lower_of_relative_errors (r X : ℕ) (hr : 1 ≤ r)
    (hX : 1 ≤ X) (hlog : 1 ≤ Real.log (X : ℝ))
    (hpsi : (5/8 : ℝ)*(X : ℝ) ≤ mangoldtSum X)
    (hD : divisorProgressionError r X X ≤
      (X : ℝ)*(Real.log X)^r/(16*(r.factorial : ℝ)))
    (hN : nonprimeMangoldtMoment (r+1) X ≤ (X : ℝ)/(16*(r.factorial : ℝ))) :
    (X : ℝ)*(Real.log X)^(r-1)/((r+1).factorial : ℝ) ≤
      shiftedPrimeMoment (r+1) X := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hlog0 : 0 < Real.log (X : ℝ) := by linarith
  have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hf' : (0 : ℝ) < (r+1).factorial := by exact_mod_cast Nat.factorial_pos (r+1)
  have hlogs : Real.log (X : ℝ) ≤ Real.log (X+1 : ℝ) :=
    Real.log_le_log hX0 (by linarith)
  have hmain : (5/8 : ℝ)*((X : ℝ)*(Real.log X)^r/(r.factorial : ℝ)) ≤
      mangoldtSum X*((Real.log (X+1 : ℝ))^r/(r.factorial : ℝ)) := by
    have h := mul_le_mul hpsi
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ hlog0.le hlogs r) hf.le)
      (by positivity : 0 ≤ (Real.log (X : ℝ))^r/(r.factorial : ℝ))
      (mangoldtSum_nonneg X)
    convert h using 1
    ring
  have hN' : nonprimeMangoldtMoment (r+1) X ≤
      (X : ℝ)*(Real.log X)^r/(16*(r.factorial : ℝ)) := by
    apply hN.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (one_le_pow₀ hlog (n := r)) hX0.le
  have h1 := mangoldtMoment_factorial_lower_with_error r X X hX
  have h2 := mangoldtMoment_le_primeMoment_add_nonprime (r+1) X
  have hhalf : (X : ℝ)*(Real.log X)^r/(2*(r.factorial : ℝ)) ≤
      Real.log X * shiftedPrimeMoment (r+1) X := by
    have hid : (X : ℝ)*(Real.log X)^r/(16*(r.factorial : ℝ)) =
        ((X : ℝ)*(Real.log X)^r/(r.factorial : ℝ))/16 := by ring
    have hid' : (X : ℝ)*(Real.log X)^r/(2*(r.factorial : ℝ)) =
        ((X : ℝ)*(Real.log X)^r/(r.factorial : ℝ))/2 := by ring
    rw [hid] at hD hN'
    rw [hid']
    linarith
  have hfactorial : (2 : ℝ)*(r.factorial : ℝ) ≤ ((r+1).factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith
  have htarget : (X : ℝ)*(Real.log X)^r/((r+1).factorial : ℝ) ≤
      Real.log X * shiftedPrimeMoment (r+1) X :=
    (div_le_div_of_nonneg_left (by positivity) (by positivity) hfactorial).trans hhalf
  apply (mul_le_mul_iff_right₀ hlog0).mp
  calc
    Real.log X * ((X : ℝ)*(Real.log X)^(r-1)/((r+1).factorial : ℝ)) =
        (X : ℝ)*(Real.log X)^r/((r+1).factorial : ℝ) := by
      have he : (Real.log (X : ℝ))^r = (Real.log X)^(r-1)*Real.log X := by
        rw [← _root_.pow_succ, Nat.sub_add_cancel hr]
      rw [he]
      ring
    _ ≤ _ := htarget

/-- Conditional eventual sharp moment. This theorem does not establish its
`RelativeFullRangeDiscrepancy` hypothesis. -/
theorem eventually_sharp_moment_of_relative_discrepancy
    (H : RelativeFullRangeDiscrepancy) (r t : ℕ) (hr : 1 ≤ r) (ht : 2 ≤ t) :
    ∀ᶠ L : ℕ in atTop,
      (momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(r-1)/
          ((r+1).factorial : ℝ) ≤ shiftedPrimeMoment (r+1) (momentScaleX t L) := by
  have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hc : (0 : ℝ) < 1/(16*(r.factorial : ℝ)) := by positivity
  have hnonprime := (tendsto_momentScaleX t (by omega)).eventually
    (eventually_nonprimeMangoldtMoment_le_linear r (1/(16*(r.factorial : ℝ))) hc)
  filter_upwards [(H r hr t ht).bound hc,
    eventually_momentScale_mangoldt_five_eighths t (by omega),
    hnonprime, eventually_ge_atTop 1] with L hD hpsi hN hL
  have hX : 1 ≤ momentScaleX t L := by unfold momentScaleX; exact Nat.one_le_pow _ _ (by omega)
  have hlog := one_le_log_momentScaleX t L (by omega) hL
  apply shiftedPrimeMoment_lower_of_relative_errors r (momentScaleX t L) hr hX hlog hpsi
  · simp only [Real.norm_eq_abs, abs_of_nonneg (divisorProgressionError_nonneg _ _ _),
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith :
        0 ≤ Real.log (momentScaleX t L : ℝ)) _))] at hD
    convert hD using 1
    ring
  · convert hN using 1
    ring

/-- Conditional implication to the exact lower-moment hypothesis used by
the smooth-prime transfer. -/
theorem sharp_dyadic_moments_of_relative_discrepancy
    (H : RelativeFullRangeDiscrepancy) : SharpDyadicMomentLower := by
  intro k hk t ht M
  have h := eventually_sharp_moment_of_relative_discrepancy H (k-1) t (by omega) ht
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at h
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨max M N, le_max_left _ _, ?_⟩
  simpa only [Nat.sub_sub, show 1+1 = 2 by omega] using hN (max M N) (le_max_right _ _)

/-- Conditional, not a settlement: the full-range weighted relative
progression-error estimate would imply the original conjecture. -/
theorem erdos_821_of_relative_discrepancy (H : RelativeFullRangeDiscrepancy) :
    ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  erdos_821_of_sharp_dyadic_moments (sharp_dyadic_moments_of_relative_discrepancy H)

end Erdos821.HigherDivisors
