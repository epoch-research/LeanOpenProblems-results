import Submission.CompositePairMinorantMean
import Submission.CorrelationVaughan

/-! The composite-only two-scale sum has a sublinear upper bound in the
admissible moving-parameter window. This demonstrates a genuine failure
of transferring its fixed-parameter mean to that window, not a failure
of the original prime-pair conjecture. -/
namespace Erdos972CompositePairWindow

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972PrimePowerError Erdos972CorrelationVaughan
open Erdos972TwoScalePairMinorant Erdos972MixedSmoothMean
open Erdos972CompositePairMinorantMean

set_option autoImplicit false
set_option maxHeartbeats 1000000

lemma pointwise_window {α t : ℝ} (hα : 1 ≤ α) (ht : 0 < t)
    {n N : ℕ} (hn : n ∈ Ioc 0 N)
    (hwindow : t*Real.log (floorMul α N) ≤ 1/4) :
    pairMinorant t n (floorMul α n) ≤ Λ n*Λ (floorMul α n) := by
  have hn0 := (mem_Ioc.mp hn).1
  have hnN := (mem_Ioc.mp hn).2
  have hgn := floorMul_pos hα hn0
  have hngN : n ≤ floorMul α N := hnN.trans (self_le_floorMul hα N)
  have hggN : floorMul α n ≤ floorMul α N := (floorMul_strictMono hα).monotone hnN
  apply pairMinorant_le ht
  · exact (mul_le_mul_of_nonneg_left
      (Real.log_le_log (Nat.cast_pos.mpr hn0) (Nat.cast_le.mpr hngN)) ht.le).trans hwindow
  · exact (mul_le_mul_of_nonneg_left
      (Real.log_le_log (Nat.cast_pos.mpr hgn) (Nat.cast_le.mpr hggN)) ht.le).trans hwindow

/-- After deleting prime coordinates, any positive contribution is
bounded by the proper-prime-power error in the finite validity window. -/
theorem composite_window_upper {α t : ℝ} (hα : 1 ≤ α) (ht : 0 < t)
    {N : ℕ} (hN : 1 ≤ N) (hwindow : t*Real.log (floorMul α N) ≤ 1/4) :
    compositePairMinorantSum t α N ≤ primePowerBudget α N := by
  classical
  have hb : compositePairMinorantSum t α N ≤
      mangoldtCorrelation α N-primeCorrelation α N := by
    unfold compositePairMinorantSum deletePrimeCoordinates mangoldtCorrelation primeCorrelation
    rw [sum_filter, ← sum_sub_distrib]
    apply sum_le_sum
    intro n hn
    by_cases hor : n.Prime ∨ (floorMul α n).Prime
    · simp only [if_pos hor]
      by_cases hand : n.Prime ∧ (floorMul α n).Prime
      · simp only [if_pos hand, vonMangoldt_apply_prime hand.1,
          vonMangoldt_apply_prime hand.2, sub_self, le_refl]
      · simp only [if_neg hand, sub_zero]
        exact mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg
    · have hand : ¬ (n.Prime ∧ (floorMul α n).Prime) := fun h => hor (Or.inl h.1)
      simp only [if_neg hor, if_neg hand, sub_zero]
      exact pointwise_window hα ht hn hwindow
  exact hb.trans (prime_power_error_bound_sharp hα hN).2

lemma parameter_tendsto_zero_of_window {α : ℝ} (hα : 1 ≤ α) (t : ℕ → ℝ)
    (ht : ∀ᶠ N : ℕ in atTop, 0 < t N)
    (hwindow : ∀ᶠ N : ℕ in atTop, t N*Real.log (floorMul α N) ≤ 1/4) :
    Tendsto t atTop (𝓝[>] 0) := by
  have hM : Tendsto (floorMul α) atTop atTop :=
    tendsto_atTop_mono (self_le_floorMul hα) tendsto_id
  have hlog : Tendsto (fun N : ℕ => Real.log (floorMul α N)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hM)
  have hb : Tendsto (fun N : ℕ => (1/4 : ℝ)/Real.log (floorMul α N)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ht⟩
  apply squeeze_zero' (ht.mono (fun N hN => hN.le)) _ hb
  filter_upwards [hwindow, eventually_ge_atTop (2 : ℕ)] with N hw hN
  have hM1 : (1 : ℝ) < floorMul α N := by
    exact_mod_cast (show 1 < floorMul α N by have := self_le_floorMul hα N; omega)
  exact (le_div_iff₀ (Real.log_pos hM1)).mpr hw

/-- This is a one-sided bound, not a claim of convergence to zero: the
composite-only signed sum can have negative contributions. -/
theorem moving_composite_upper {α : ℝ} (hα : 1 ≤ α) (t : ℕ → ℝ)
    (ht : ∀ᶠ N : ℕ in atTop, 0 < t N)
    (hwindow : ∀ᶠ N : ℕ in atTop, t N*Real.log (floorMul α N) ≤ 1/4)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, compositePairMinorantSum (t N) α N/(N : ℝ) < ε := by
  have hb := (tendsto_order.mp (primePowerBudget_div_tendsto hα)).2 ε hε
  filter_upwards [ht, hwindow, hb, eventually_ge_atTop (1 : ℕ)] with N ht hw hb hN
  exact (div_le_div_of_nonneg_right (composite_window_upper hα ht hN hw)
    (Nat.cast_nonneg (α := ℝ) N)).trans_lt hb

/-- An actual normalized error lower bound throughout the moving window.
It concerns the COMPOSITE-ONLY expression, not the full pair minorant. -/
theorem moving_composite_mean_gap {α : ℝ} (hα : 1 ≤ α) (t : ℕ → ℝ)
    (ht : ∀ᶠ N : ℕ in atTop, 0 < t N)
    (hwindow : ∀ᶠ N : ℕ in atTop, t N*Real.log (floorMul α N) ≤ 1/4) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ)/4 < |compositePairMinorantSum (t N) α N-(N : ℝ)*pairMean (t N)| := by
  have hmean := pairMean_tendsto.comp (parameter_tendsto_zero_of_window hα t ht hwindow)
  have hm := (tendsto_order.mp hmean).1 (1/3) (by norm_num)
  have hc := moving_composite_upper hα t ht hwindow (ε := 1/12) (by norm_num)
  filter_upwards [hm, hc, eventually_ge_atTop (1 : ℕ)] with N hm hc hN
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hc' := (div_lt_iff₀ hNR).mp hc
  have hm' := mul_lt_mul_of_pos_left hm hNR
  simp only [Function.comp_apply] at hm'
  have hg : (N : ℝ)/4 < (N : ℝ)*pairMean (t N)-compositePairMinorantSum (t N) α N := by
    nlinarith only [hc', hm']
  exact hg.trans_le (by
    simpa only [neg_sub] using neg_le_abs
      (compositePairMinorantSum (t N) α N-(N : ℝ)*pairMean (t N)))

#print axioms composite_window_upper
#print axioms parameter_tendsto_zero_of_window
#print axioms moving_composite_upper
#print axioms moving_composite_mean_gap

end Erdos972CompositePairWindow
