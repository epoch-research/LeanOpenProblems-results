import Submission.MixedComplementRectangle
import Submission.ThinSubpowerBand

/-! Uniform restoration of the mixed rectangle to its factored weighted
short-prefix expression, in mean absolute value. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma mixedRectangle_point_error (B D W F X k L N n : ℕ)
    (hB : 1 < B) (hW : 1 < W) (hWN : N+1 ≤ W^L)
    (hBW : B ≤ W) (hBk : B^k ≤ W) (hn : 0 < n) (hnN : n ≤ N) (hF : F ≤ B^k) :
    |mixedComplementRectangleAt B D W F X n-highDivisorWeight W X n*untruncatedComplementPrefix B F n| ≤
      2*(2 : ℝ)^(2*L)*
        ((if (activeBlockPrimes (largePrimeSet B W) (activePrimeAtoms (largePrimeSet B W) n)).card ≤ k then
            (2 : ℝ)^(activeBlockPrimes (largePrimeSet B (B^k)) (activePrimeAtoms (largePrimeSet B (B^k)) n)).card else 0)+
          (if roughRadical B (n*(n+1)) ≤ D*(B^k*X) then
            (2 : ℝ)^(activeBlockPrimes (largePrimeSet B (B^k)) (activePrimeAtoms (largePrimeSet B (B^k)) n)).card else 0)) := by
  have ha := mixedComplementRectangleAt_abs_le B D W F X k L N n hB hW hWN hn hnN hF
  have hw := (high_weight_and_complement_bound W L N n B D X hW hWN hn hnN).1
  have hp := (untruncatedComplementPrefix_abs_le B (B^k) k F n hB hn hF le_rfl).trans
    (subsetPolynomial_le_two_pow k _)
  have hprod := mul_le_mul hw hp (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 2^(2*L))
  rw [← abs_mul] at hprod
  have hh := (abs_sub _ _).trans (add_le_add ha hprod)
  have hb : |mixedComplementRectangleAt B D W F X n-highDivisorWeight W X n*untruncatedComplementPrefix B F n| ≤
      2*(2 : ℝ)^(2*L)*(2 : ℝ)^(activeBlockPrimes (largePrimeSet B (B^k))
        (activePrimeAtoms (largePrimeSet B (B^k)) n)).card := by linarith
  by_cases ht : (activeBlockPrimes (largePrimeSet B W) (activePrimeAtoms (largePrimeSet B W) n)).card ≤ k
  · rw [if_pos ht]
    apply hb.trans
    split_ifs <;> nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (2*L),
      pow_pos (by norm_num : (0 : ℝ) < 2) (activeBlockPrimes (largePrimeSet B (B^k))
        (activePrimeAtoms (largePrimeSet B (B^k)) n)).card]
  · rw [if_neg ht,zero_add]
    by_cases hr : roughRadical B (n*(n+1)) ≤ D*(B^k*X)
    · rw [if_pos hr]
      exact hb
    · rw [if_neg hr,mul_zero,mixedComplementRectangleAt_factor B D W F X k n hB hn hBW hBk hF
        (by omega) (by omega),sub_self,abs_zero]

/-- F may be chosen adversarially after N: the absolute-error estimate is
uniform for all short-factor endpoints F≤B(N)^k. -/
theorem mixedRectangle_mean_error_uniform (B D W X : ℕ → ℕ) (k L : ℕ) (hL : 0 < L)
    (hBt : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hW : ∀ᶠ N in atTop, 1 < W N ∧ N+1 ≤ (W N)^L)
    (hsize : ∀ᶠ N in atTop, (D N*((B N)^k*X N))^2 ≤ (N+1)^3) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ F ≤ (B N)^k,
      (∑ n ∈ range N, |mixedComplementRectangleAt (B N) (D N) (W N) F (X N) (n+1)-
        highDivisorWeight (W N) (X N) (n+1)*untruncatedComplementPrefix (B N) F (n+1)|)/N < ε := by
  have hWP := subpower_below_power_cutoff B W L hL hB (hW.mono fun N h => h.2)
  have hthin := thin_subpower_band_zero B W k hBt hB hWP
  have hthin' : Tendsto (fun N : ℕ => (∑ n ∈ range N, if
      (activeBlockPrimes (largePrimeSet (B N) (W N)) (activePrimeAtoms (largePrimeSet (B N) (W N)) (n+1))).card ≤ k
      then (1 : ℝ) else 0)/N) atTop (𝓝 0) := by
    apply shifted_indicator_mean_zero (fun N n => (activeBlockPrimes (largePrimeSet (B N) (W N))
      (activePrimeAtoms (largePrimeSet (B N) (W N)) n)).card ≤ k)
    simpa only [sum_boole,thinPrimeBlockCount] using hthin
  have hrad := rough_radical_small_proportion_zero B (fun N => D N*((B N)^k*X N)) hBt hB hsize
  have hrad' := shifted_indicator_mean_zero
    (fun N n => roughRadical (B N) (n*(n+1)) ≤ D N*((B N)^k*X N)) hrad
  have ht := short_band_exp_exception_zero B k
    (fun N n => (activeBlockPrimes (largePrimeSet (B N) (W N))
      (activePrimeAtoms (largePrimeSet (B N) (W N)) (n+1))).card ≤ k) hBt hthin'
  have hr := short_band_exp_exception_zero B k
    (fun N n => roughRadical (B N) ((n+1)*((n+1)+1)) ≤ D N*((B N)^k*X N)) hBt hrad'
  have hbound := (ht.add hr).const_mul (2*(2 : ℝ)^(2*L))
  simp only [add_zero,mul_zero] at hbound
  intro ε hε
  filter_upwards [hBt.eventually_gt_atTop 1,hW,hWP 1,hWP k,hbound.eventually_lt_const hε]
    with N hb hw hbw hbk he
  simp only [pow_one] at hbw
  intro F hF
  have hs := sum_le_sum (s := range N) (fun n hn => mixedRectangle_point_error (B N) (D N) (W N) F
    (X N) k L N (n+1) hb hw.1 hw.2 hbw hbk (by omega) (by have := mem_range.mp hn; omega) hF)
  simp only [← mul_sum,sum_add_distrib] at hs
  apply lt_of_le_of_lt (div_le_div_of_nonneg_right hs (Nat.cast_nonneg (α := ℝ) N))
  convert he using 1; ring

#print axioms mixedRectangle_mean_error_uniform
end Erdos371
