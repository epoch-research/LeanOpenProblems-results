import Submission.SuccessorSupplyBudget

/-!
# Fixed numerical scale comparisons for the successor supply

The predecessor quotient lies between two nearby power scales. This
supplies the long-cofactor threshold and makes the short-tail error
exponentially negligible uniformly in the progression modulus.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

lemma successor_supply_quotient_bounds (m X d : ℕ)
    (hXlo : independentN 400020 m ≤ X) (hXhi : X ≤ independentN 400021 m)
    (hdlo : independentN 200000 m ≤ d) (hdhi : d ≤ independentN 200004 m) :
    2^(128*100008*m) ≤ X/d ∧ X/d ≤ 2^(128*100011*m) := by
  have hd : 0 < d := (by unfold independentN; positivity : 0 < independentN 200000 m).trans_le hdlo
  constructor
  · apply (Nat.le_div_iff_mul_le hd).mpr
    apply (Nat.mul_le_mul_left _ hdhi).trans
    apply le_trans _ hXlo
    simp only [independentN,← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    omega
  · have hmul : X ≤ 2^(128*100011*m)*d := by
      apply hXhi.trans
      apply le_trans _ (Nat.mul_le_mul_left _ hdlo)
      simp only [independentN,← pow_add]
      apply Nat.pow_le_pow_right (by decide)
      omega
    apply (Nat.div_le_div_right hmul).trans_eq
    exact Nat.mul_div_cancel _ hd

lemma successor_supply_long_threshold (m H : ℕ) (hm : 2 ≤ m)
    (hH : 2^(128*100008*m) ≤ H) :
    cofactorScale 3 (2*cofactorDyadicIndex 200003 (128*99999*m)) ≤ H/2^(128*99999*m) := by
  have hh := (cofactorDyadicIndex_bounds 200003 (128*99999*m) (by decide)).2
  have he : 1536*cofactorDyadicIndex 200003 (128*99999*m) ≤ 1152*m := by
    nlinarith only [hh,hm]
  have hscale : cofactorScale 3 (2*cofactorDyadicIndex 200003 (128*99999*m)) ≤ 2^(1152*m) := by
    have hs : cofactorScale 3 (2*cofactorDyadicIndex 200003 (128*99999*m)) =
        2^(1536*cofactorDyadicIndex 200003 (128*99999*m)) := by
      unfold cofactorScale progressionScaleN
      congr 1
      ring
    rw [hs]
    exact Nat.pow_le_pow_right (by decide) he
  apply hscale.trans
  apply (Nat.le_div_iff_mul_le (by positivity : 0<2^(128*99999*m))).mpr
  apply le_trans _ hH
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  omega

lemma successor_supply_log_upper (m X : ℕ) (hX : X ≤ independentN 400021 m) :
    Real.log (X : ℝ) ≤ 64*400021*(m : ℝ)*Real.log 2 := by
  have hh := log_nat_mono hX
  simpa only [independentN,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_mul,Real.log_pow] using hh

lemma not_prime_two_pow (e : ℕ) (he : 2 ≤ e) : ¬(2^e).Prime := by
  intro hp
  have hd : 2 ∣ 2^e := dvd_pow_self 2 (by omega)
  have hh := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd
  have hfour : 4 ≤ 2^e := by
    simpa only [show (2 : ℕ)^2=4 by decide] using Nat.pow_le_pow_right (by decide : 1 ≤ 2) he
  omega

lemma successor_supply_smooth_cutoff_not_prime (m : ℕ) (hm : 1 ≤ m) :
    ¬(independentN 180000 m).Prime := by
  apply not_prime_two_pow
  omega

noncomputable def successorTailError (m : ℕ) : ℝ :=
  (2 : ℝ)^(1536*m)*((2 : ℝ)^(6399936*m)+(2 : ℝ)^(1599984*m)+1)

lemma successorTailError_nonneg (m : ℕ) : 0 ≤ successorTailError m := by
  unfold successorTailError
  positivity

lemma successorTailError_le (m : ℕ) : successorTailError m ≤ 3*(2 : ℝ)^(6401472*m) := by
  have h1 : (2 : ℝ)^(1599984*m) ≤ (2 : ℝ)^(6399936*m) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (1 : ℝ) ≤ 2^(6399936*m) := one_le_pow₀ (by norm_num)
  have hh := mul_le_mul_of_nonneg_left (_root_.add_le_add (_root_.add_le_add (le_refl ((2 : ℝ)^(6399936*m))) h1) h2)
    (show (0 : ℝ) ≤ 2^(1536*m) by positivity)
  have he : (2 : ℝ)^(1536*m)*(2 : ℝ)^(6399936*m)=(2 : ℝ)^(6401472*m) := by
    rw [← pow_add]
    congr 1
    omega
  unfold successorTailError
  nlinarith only [hh,he]

lemma eventually_successor_tail_error :
    ∀ᶠ m : ℕ in atTop, ∀ X H : ℕ, X ≤ independentN 400021 m →
      2^(128*100008*m) ≤ H →
        Real.log (X : ℝ)*successorTailError m ≤ (H : ℝ)/100 := by
  filter_upwards [eventually_nat_poly_le_two_pow 1 (300*25601344) 1] with m hm
  intro X H hX hH
  have hpoly : (300*25601344 : ℝ)*(m : ℝ) ≤ (2 : ℝ)^m := by
    have hh : (300*25601344 : ℝ)*((m : ℝ)+1) ≤ (2 : ℝ)^m := by
      exact_mod_cast (by simpa only [one_mul,pow_one] using hm)
    nlinarith only [hh]
  have hlog : Real.log (X : ℝ) ≤ 25601344*(m : ℝ) := by
    have hh := successor_supply_log_upper m X hX
    have hl2 : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hmul := mul_le_mul_of_nonneg_left hl2 (show (0 : ℝ) ≤ 64*400021*m by positivity)
    nlinarith only [hh,hmul]
  have herr := mul_le_mul hlog (successorTailError_le m) (successorTailError_nonneg m)
    (show (0 : ℝ) ≤ 25601344*m by positivity)
  have hscaled := mul_le_mul_of_nonneg_right hpoly (show (0 : ℝ) ≤ 2^(6401472*m) by positivity)
  have hpow : (2 : ℝ)^m*(2 : ℝ)^(6401472*m) ≤ (H : ℝ) := by
    rw [← pow_add]
    apply le_trans _ (Nat.cast_le.mpr hH)
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  nlinarith only [herr,hscaled,hpow]

end Erdos821.AnalyticSieve
