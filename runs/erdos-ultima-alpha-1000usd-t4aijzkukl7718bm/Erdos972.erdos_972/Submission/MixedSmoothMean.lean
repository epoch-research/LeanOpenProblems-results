import Submission.OrdinaryDampedCorrelation
import Submission.TwoScalePairMinorant

/-! Mixed fixed-positive-parameter smooth correlation means. No uniformity
as either parameter tends to zero with the input cutoff is asserted. -/
namespace Erdos972MixedSmoothMean

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972PrimePowerError Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive
open Erdos972SmoothDivisorTail Erdos972UniformSmoothCorrelationTail
open Erdos972FixedDampedCorrelation Erdos972OrdinaryDivisorMean
open Erdos972DivisorCovariance Erdos972DampedMeanZeta Erdos972TwoScalePairMinorant

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def mixedExpCorrelation (s t α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, expDivisorSum s n * expDivisorSum t (floorMul α n)

noncomputable def mixedTruncatedCorrelation (s t α : ℝ) (D N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, truncatedExpSum s D n * truncatedExpSum t D (floorMul α n)

noncomputable def mixedSmoothCorrelation (s t α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, smoothMangoldt s n * smoothMangoldt t (floorMul α n)

lemma mixed_error_of_energy {α s t δ η : ℝ}
    (hα : 1 ≤ α) (hs : 0 ≤ s) (ht : 0 ≤ t) (hδ : 0 ≤ δ) (hη : 0 < η)
    (D N : ℕ)
    (hboundS : ∀ M : ℕ, (∑ n ∈ Ioc 0 M, (expTail s D n)^2) ≤ δ*M)
    (hboundT : ∀ M : ℕ, (∑ n ∈ Ioc 0 M, (expTail t D n)^2) ≤ δ*M) :
    |mixedExpCorrelation s t α N-mixedTruncatedCorrelation s t α D N| ≤
      (2*η+(1/η+1)*δ*(1+α))*N := by
  have hp (n : ℕ) :
      |expDivisorSum s n*expDivisorSum t (floorMul α n)-
        truncatedExpSum s D n*truncatedExpSum t D (floorMul α n)| ≤
        2*η+(1/η+1)*((expTail s D n)^2+(expTail t D (floorMul α n))^2) :=
    pair_perturbation_energy (expDivisorSum_nonneg hs _) (expDivisorSum_le_one hs _)
      (expDivisorSum_nonneg ht _) (expDivisorSum_le_one ht _) hη
  unfold mixedExpCorrelation mixedTruncatedCorrelation
  rw [← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ n ∈ Ioc 0 N,
        (2*η+(1/η+1)*((expTail s D n)^2+(expTail t D (floorMul α n))^2)) :=
      sum_le_sum (fun n _ => hp n)
    _ = (N : ℝ)*(2*η) + (1/η+1)*
        ((∑ n ∈ Ioc 0 N, (expTail s D n)^2)+
          ∑ n ∈ Ioc 0 N, (expTail t D (floorMul α n))^2) := by
      simp only [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
      ring
    _ ≤ (N : ℝ)*(2*η)+(1/η+1)*(δ*N+δ*α*N) := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left
        (add_le_add (hboundS N) (output_tail_energy hα hδ D N hboundT))
        (show 0 ≤ 1/η+1 by positivity)) _
    _ = _ := by ring

lemma eventually_mixed_uniform_cutoff {α s t ε : ℝ}
    (hα : 1 ≤ α) (hs : 0 < s) (ht : 0 < t) (hε : 0 < ε) :
    ∀ᶠ D : ℕ in atTop, ∀ N : ℕ,
      |mixedExpCorrelation s t α N-mixedTruncatedCorrelation s t α D N| ≤ ε*N := by
  let η := ε/4
  let δ := ε/(2*(1/η+1)*(1+α))
  have hη : 0 < η := by dsimp [η]; positivity
  have hc : 0 < 1/η+1 := by positivity
  have hαc : 0 < 1+α := by linarith
  have hδ : 0 < δ := div_pos hε (by positivity)
  filter_upwards [eventually_uniform_tail_cutoff hs hδ,
    eventually_uniform_tail_cutoff ht hδ] with D hS hT N
  have hh := mixed_error_of_energy hα hs.le ht.le hδ.le hη D N hS hT
  have he : 2*η+(1/η+1)*δ*(1+α) = ε := by
    dsimp only [δ]
    field_simp
    dsimp only [η]
    ring
  rwa [he] at hh

lemma mixed_divisor_mean_expansion (D : ℕ) (a b : ℕ → ℝ) :
    divisorMean D a * divisorMean D b =
      ∑ d ∈ Ioc 0 D, ∑ e ∈ Ioc 0 D, a d*b e*(1/((d : ℝ)*e)) := by
  rw [divisorMean, divisorMean, sum_mul_sum]
  apply sum_congr rfl
  intro d _
  apply sum_congr rfl
  intro e _
  ring

lemma mixed_truncated_mean {α : ℝ} (hα : 1 ≤ α) (hI : Irrational α)
    (s t : ℝ) (D : ℕ) :
    Tendsto (fun N : ℕ => mixedTruncatedCorrelation s t α D N/(N : ℝ)) atTop
      (𝓝 (divisorMean D (dampedCoefficient s)*divisorMean D (dampedCoefficient t))) := by
  have hh := tendsto_finset_sum (Ioc 0 D) (fun d hd =>
    tendsto_finset_sum (Ioc 0 D) (fun e he =>
      (divisorPairs_mean (show 0 ≤ α by linarith) hI (mem_Ioc.mp hd).1 (mem_Ioc.mp he).1).const_mul
        (dampedCoefficient s d*dampedCoefficient t e)))
  rw [← mixed_divisor_mean_expansion] at hh
  convert hh using 1
  funext N
  have hpoly : mixedTruncatedCorrelation s t α D N =
      ∑ n ∈ Ioc 0 N, divisorPolynomial D (dampedCoefficient s) n *
        divisorPolynomial D (dampedCoefficient t) (floorMul α n) := by
    apply sum_congr rfl
    intro n hn
    rw [truncatedExpSum_eq_polynomial s D (mem_Ioc.mp hn).1.ne',
      truncatedExpSum_eq_polynomial t D (floorMul_pos hα (mem_Ioc.mp hn).1).ne']
  rw [hpoly, polynomial_pair_expansion]
  simp only [sum_div, mul_div_assoc]

/-- A genuine mixed-parameter mean along all natural cutoffs, with both
positive parameters fixed before the limit. -/
theorem mixed_exp_mean {α s t : ℝ} (hα : 1 ≤ α) (hI : Irrational α)
    (hs : 0 < s) (ht : 0 < t) :
    Tendsto (fun N : ℕ => mixedExpCorrelation s t α N/(N : ℝ)) atTop
      (𝓝 (dampedMean s*dampedMean t)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hthird : 0 < ε/3 := by positivity
  have hma := (((divisorMean_tendsto hs).mul (divisorMean_tendsto ht)).sub_const
    (dampedMean s*dampedMean t)).abs
  simp only [sub_self, abs_zero] at hma
  obtain ⟨D, hD, hmean⟩ := ((eventually_mixed_uniform_cutoff hα hs ht hthird).and
    ((tendsto_order.mp hma).2 (ε/3) hthird)).exists
  have htr := (Metric.tendsto_nhds.mp (mixed_truncated_mean hα hI s t D)) (ε/3) hthird
  filter_upwards [htr, eventually_ge_atTop (1 : ℕ)] with N htr hN
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have htail : |mixedExpCorrelation s t α N/(N : ℝ)-
      mixedTruncatedCorrelation s t α D N/(N : ℝ)| ≤ ε/3 := by
    rw [← sub_div, abs_div, abs_of_pos hNR]
    exact (div_le_iff₀ hNR).mpr (hD N)
  rw [Real.dist_eq] at htr ⊢
  have hh := (abs_sub_le (mixedExpCorrelation s t α N/(N : ℝ))
    (mixedTruncatedCorrelation s t α D N/(N : ℝ)) (dampedMean s*dampedMean t)).trans
    (add_le_add htail (abs_sub_le _
      (divisorMean D (dampedCoefficient s)*divisorMean D (dampedCoefficient t)) _))
  linarith only [hh, htr, hmean]

lemma mixed_unit_correction {α s t : ℝ} (hα : 1 ≤ α) (hs : 0 < s) (ht : 0 < t)
    (N : ℕ) :
    |mixedExpCorrelation s t α N - s*t*mixedSmoothCorrelation s t α N| ≤ 1 := by
  have he (u : ℝ) (hu : 0 < u) (n : ℕ) (hn : n ≠ 1) :
      expDivisorSum u n = u*smoothMangoldt u n := by
    rw [smoothMangoldt, expDivisorSum_at_zero, one_apply, if_neg hn, sub_zero]
    field_simp
  have hterm (n : ℕ) (hn : n ∈ Ioc 0 N) (hn1 : n ≠ 1) :
      expDivisorSum s n*expDivisorSum t (floorMul α n)-
        s*t*(smoothMangoldt s n*smoothMangoldt t (floorMul α n)) = 0 := by
    have hg1 : floorMul α n ≠ 1 := by
      have hng := self_le_floorMul hα n
      have hn0 := (mem_Ioc.mp hn).1
      omega
    rw [he s hs n hn1, he t ht _ hg1]
    ring
  unfold mixedExpCorrelation mixedSmoothCorrelation
  rw [mul_sum, ← sum_sub_distrib]
  by_cases hN : 1 ∈ Ioc 0 N
  · rw [sum_eq_single 1 (fun n hn hne => hterm n hn hne) (fun h => (h hN).elim)]
    have hS : smoothMangoldt s 1 = 0 := by simp [smoothMangoldt, expDivisorSum]
    have hE : expDivisorSum s 1 = 1 := by simp [expDivisorSum]
    simp only [hS, hE, one_mul, zero_mul, mul_zero, sub_zero]
    rw [abs_of_nonneg (expDivisorSum_nonneg ht.le _)]
    exact expDivisorSum_le_one ht.le _
  · have hz : (∑ n ∈ Ioc 0 N,
        (expDivisorSum s n*expDivisorSum t (floorMul α n)-
          s*t*(smoothMangoldt s n*smoothMangoldt t (floorMul α n)))) = 0 := by
      apply sum_eq_zero
      intro n hn
      exact hterm n hn (fun h => hN (h ▸ hn))
    rw [hz, abs_zero]
    norm_num

theorem mixed_smooth_mean {α s t : ℝ} (hα : 1 ≤ α) (hI : Irrational α)
    (hs : 0 < s) (ht : 0 < t) :
    Tendsto (fun N : ℕ => mixedSmoothCorrelation s t α N/(N : ℝ)) atTop
      (𝓝 ((dampedMean s/s)*(dampedMean t/t))) := by
  have he : Tendsto (fun N : ℕ =>
      (mixedExpCorrelation s t α N-s*t*mixedSmoothCorrelation s t α N)/(N : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    filter_upwards with N
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
    exact div_le_div_of_nonneg_right (mixed_unit_correction hα hs ht N) (Nat.cast_nonneg N)
  have hh := ((mixed_exp_mean hα hI hs ht).sub he).div_const (s*t)
  simp only [sub_zero] at hh
  convert hh using 1
  · funext N
    field_simp
    ring
  · congr 1
    ring

noncomputable def pairMean (t : ℝ) : ℝ :=
  (32/63)*(7*(dampedMean t/t)^2-
    6*(dampedMean t/t)*(dampedMean (2*t)/(2*t)))

lemma pairMinorantSum_eq_mixed (t α : ℝ) (N : ℕ) :
    pairMinorantSum t α N = (32/63)*(7*mixedSmoothCorrelation t t α N-
      3*(mixedSmoothCorrelation (2*t) t α N+mixedSmoothCorrelation t (2*t) α N)) := by
  simp only [pairMinorantSum, pairMinorant, mixedSmoothCorrelation,
    mul_sub, mul_add, mul_assoc, sum_sub_distrib, sum_add_distrib, ← mul_sum]

/-- This establishes the previously formal fixed-parameter benchmark. It
still does not assert a mean theorem in the finite minorant window. -/
theorem pairMinorant_fixed_mean {α t : ℝ} (hα : 1 ≤ α) (hI : Irrational α) (ht : 0 < t) :
    Tendsto (fun N : ℕ => pairMinorantSum t α N/(N : ℝ)) atTop (𝓝 (pairMean t)) := by
  have ht2 : 0 < 2*t := by positivity
  have hh := (((mixed_smooth_mean hα hI ht ht).const_mul 7).sub
    (((mixed_smooth_mean hα hI ht2 ht).add
      (mixed_smooth_mean hα hI ht ht2)).const_mul 3)).const_mul (32/63)
  convert hh using 1
  · funext N
    rw [pairMinorantSum_eq_mixed]
    ring
  · unfold pairMean
    congr 1
    ring

lemma double_parameter_tendsto :
    Tendsto (fun t : ℝ => 2*t) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hh : Tendsto (fun t : ℝ => 2*t) (𝓝 0) (𝓝 (2*0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    simpa only [mul_zero] using hh.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    change 0 < 2*t
    positivity

/-- The scalar mean tends to a positive constant in the OUTER limit.
The inner cutoff limit always holds the parameter fixed. -/
theorem pairMean_tendsto :
    Tendsto pairMean (𝓝[>] 0) (𝓝 (32/63 : ℝ)) := by
  have ha := dampedMean_div_tendsto_one
  have hb := dampedMean_div_tendsto_one.comp double_parameter_tendsto
  have hh := (((ha.pow 2).const_mul 7).sub ((ha.mul hb).const_mul 6)).const_mul (32/63)
  norm_num only [one_pow, mul_one, sub_self, Function.comp_apply] at hh
  convert hh using 1
  funext t
  unfold pairMean
  ring

/-- Actual eventual linear positivity at fixed small t. There is NO
claim that these large N satisfy t log(floor(alpha*N)) <= 1/4. -/
theorem eventually_fixed_linear_pairMinorant {α : ℝ} (hα : 1 ≤ α) (hI : Irrational α) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ᶠ N : ℕ in atTop,
      (N : ℝ)/4 < pairMinorantSum t α N := by
  have hm := (tendsto_order.mp pairMean_tendsto).1 (1/3) (by norm_num)
  filter_upwards [self_mem_nhdsWithin, hm] with t ht hm
  change 0 < t at ht
  have hl := (tendsto_order.mp (pairMinorant_fixed_mean hα hI ht)).1 (1/4)
    (show (1/4 : ℝ) < pairMean t by linarith only [hm])
  filter_upwards [hl, eventually_ge_atTop (1 : ℕ)] with N hN hN1
  have hh := (lt_div_iff₀ (Nat.cast_pos.mpr hN1 : (0 : ℝ) < N)).mp hN
  linarith only [hh]

#print axioms mixed_exp_mean
#print axioms mixed_smooth_mean
#print axioms pairMinorant_fixed_mean
#print axioms pairMean_tendsto
#print axioms eventually_fixed_linear_pairMinorant

end Erdos972MixedSmoothMean
