import Submission.RoughHalfError
import Submission.ChebyshevFactorialLower

/-!
# Normalized progression limits for fixed rough modulus pools

The main term is normalized by the actual Mangoldt sum, so no prime number
theorem is assumed. A fixed strict half-level margin is retained.
-/
open Nat Finset Filter ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

lemma tendsto_succ_pow_div_two_pow (k : ℕ) :
    Tendsto (fun m : ℕ => ((m : ℝ)+1)^k/(2 : ℝ)^m) atTop (𝓝 0) := by
  have hsucc : Tendsto (fun m : ℕ => m+1) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_succ m) tendsto_id
  have h := ((tendsto_pow_const_div_const_pow_of_one_lt k
    (by norm_num : (1 : ℝ)<2)).comp hsucc).const_mul 2
  simp only [mul_zero] at h
  convert h using 1
  funext m
  dsimp only [Function.comp_apply]
  simp only [Nat.cast_add, Nat.cast_one, _root_.pow_succ]
  field_simp

lemma total_pool_progression_discrepancy (D : Finset ℕ) (N : ℕ)
    (hD : ∀ d ∈ D, 0 < d) :
    |(∑ d ∈ D, residueOneMangoldt d N)-mangoldtSum N*poolTotientMass D| ≤
      ∑ d ∈ D, compositeProgressionError d N := by
  unfold poolTotientMass
  rw [mul_sum, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro d hd
  simpa only [div_eq_mul_inv] using composite_progression_discrepancy d N (hD d hd)

lemma progressionScaleN_mul_tendsto (t : ℕ) (ht : 1 ≤ t) :
    Tendsto (fun m => progressionScaleN (t*m)) atTop atTop := by
  apply (tendsto_pow_atTop_atTop_of_one_lt (by decide : (1 : ℕ)<2)).comp
  change Tendsto (fun m : ℕ => 64*(t*m)) atTop atTop
  apply tendsto_atTop_mono (fun m => ?_) tendsto_id
  exact (Nat.le_mul_of_pos_left m ht).trans (Nat.le_mul_of_pos_left (t*m) (by decide))

/-- Arbitrary rough pools, not just products of a prescribed number of primes. -/
theorem tendsto_rough_pool_normalized_error (D : ℕ → Finset ℕ) (a b t : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (ht : 22 ≤ t) (hbt : 2*b+5 ≤ t)
    (hD : ∀ m : ℕ, 1 ≤ m → ∀ d ∈ D m, 0 < d ∧ d ≤ progressionScaleN (b*m))
    (hrough : ∀ m : ℕ, 1 ≤ m → ∀ d ∈ D m, ∀ c ∈ d.divisors.erase 1,
      progressionScaleN (a*m) ≤ c) :
    Tendsto (fun m => (∑ d ∈ D m, residueOneMangoldt d (progressionScaleN (t*m)))/
      mangoldtSum (progressionScaleN (t*m))-poolTotientMass (D m)) atTop (𝓝 0) := by
  let C : ℝ := 1000000000000000
  have hlim := (tendsto_succ_pow_div_two_pow 7).const_mul (2*C*((t : ℝ)+1)^7)
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1,
    (progressionScaleN_mul_tendsto t (by omega)).eventually eventually_mangoldt_nine_tenths]
    with m hm hpsi
  let N := progressionScaleN (t*m)
  let F : ℝ := (2 : ℝ)^((64*t-1)*m)
  let Z : ℝ := ((t : ℝ)+1)*((m : ℝ)+1)
  have hN : (0 : ℝ)<N := by dsimp [N,progressionScaleN]; positivity
  have hpsi' : (N : ℝ)/2 ≤ mangoldtSum N := by
    change (9/10 : ℝ)*(N : ℝ) ≤ mangoldtSum N at hpsi
    linarith only [hpsi,hN]
  have hpsi0 : 0 < mangoldtSum N := lt_of_lt_of_le (half_pos hN) hpsi'
  have hnum : |(∑ d ∈ D m, residueOneMangoldt d N)-mangoldtSum N*poolTotientMass (D m)| ≤ C*Z^7*F := by
    have hmain := total_pool_progression_discrepancy (D m) N (fun d hd => (hD m hm d hd).1)
    have hh := rough_pool_below_half_combined_error (D m) a b t m ha hab ht hm hbt
      (hD m hm) (hrough m hm)
    have hp : 0 ≤ 2*(progressionScaleN (b*m) : ℝ)*Real.sqrt N*Real.log N := by
      positivity
    change _ ≤ C*Z^7*F at hh
    exact hmain.trans (by linarith only [hh,hp])
  have he : (∑ d ∈ D m, residueOneMangoldt d N)/mangoldtSum N-poolTotientMass (D m) =
      ((∑ d ∈ D m, residueOneMangoldt d N)-mangoldtSum N*poolTotientMass (D m))/mangoldtSum N := by
    field_simp
  have hpow : F*(2 : ℝ)^m = (N : ℝ) := by
    simp only [F,N,progressionScaleN,Nat.cast_pow,Nat.cast_ofNat,← pow_add]
    congr 1
    have hh := Nat.sub_add_cancel (by omega : 1 ≤ 64*t)
    nlinarith only [congrArg (fun z : ℕ => z*m) hh]
  change ‖(∑ d ∈ D m, residueOneMangoldt d N)/mangoldtSum N-poolTotientMass (D m)‖ ≤ _
  rw [Real.norm_eq_abs,he,abs_div,abs_of_pos hpsi0]
  calc
    _ ≤ (C*Z^7*F)/mangoldtSum N := div_le_div_of_nonneg_right hnum hpsi0.le
    _ ≤ (C*Z^7*F)/((N : ℝ)/2) :=
      div_le_div_of_nonneg_left (by dsimp [C,Z,F]; positivity) (half_pos hN) hpsi'
    _ = _ := by
      rw [← hpow]
      dsimp [Z]
      simp only [mul_pow]
      field_simp [show F ≠ 0 by dsimp [F]; positivity]

/-- A limiting reciprocal-totient mass transfers to normalized progression weight. -/
theorem tendsto_rough_pool_progression_normalized (D : ℕ → Finset ℕ) (a b t : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (ht : 22 ≤ t) (hbt : 2*b+5 ≤ t)
    (hD : ∀ m : ℕ, 1 ≤ m → ∀ d ∈ D m, 0 < d ∧ d ≤ progressionScaleN (b*m))
    (hrough : ∀ m : ℕ, 1 ≤ m → ∀ d ∈ D m, ∀ c ∈ d.divisors.erase 1,
      progressionScaleN (a*m) ≤ c) (W : ℝ)
    (hW : Tendsto (fun m => poolTotientMass (D m)) atTop (𝓝 W)) :
    Tendsto (fun m => (∑ d ∈ D m, residueOneMangoldt d (progressionScaleN (t*m)))/
      mangoldtSum (progressionScaleN (t*m))) atTop (𝓝 W) := by
  have hh := (tendsto_rough_pool_normalized_error D a b t ha hab ht hbt hD hrough).add hW
  simpa only [sub_add_cancel, zero_add] using hh

end Erdos821
