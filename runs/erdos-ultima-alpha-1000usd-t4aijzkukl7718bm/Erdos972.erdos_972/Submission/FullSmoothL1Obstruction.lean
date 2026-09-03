import Submission.DampedSingleMean

/-! The full smoothed Mangoldt function is not an L1 approximation uniform
in the input cutoff. Its fixed-parameter L1 error has an exact positive
mean, despite pointwise convergence as the parameter tends to zero. This
is a limitation of an absolute-error proof strategy, not a disproof of
Erdos 972 and not a signed prime-pair correlation estimate. -/
namespace Erdos972FullSmoothL1Obstruction

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive
open Erdos972SmoothDivisorTail Erdos972DampedSingleMean
open Erdos972FixedDampedCorrelation Erdos972DampedMeanZeta Erdos972ChebyshevPNT

lemma smoothMangoldt_le_inv {t : ℝ} (ht : 0 < t) (n : ℕ) :
    smoothMangoldt t n ≤ 1/t := by
  by_cases hn : n = 1
  · simpa [hn, smoothMangoldt, expDivisorSum] using (one_div_nonneg.mpr ht.le)
  rw [smoothMangoldt, expDivisorSum_at_zero, one_apply, if_neg hn, sub_zero]
  exact div_le_div_of_nonneg_right (expDivisorSum_le_one ht.le n) ht.le

lemma prime_card_eq (N : ℕ) : ((Ioc 0 N).filter Nat.Prime).card = N.primeCounting := by
  have he : (Ioc 0 N).filter Nat.Prime = (N+1).primesBelow := by
    ext p
    simp only [mem_filter, mem_Ioc, Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨hp0, hpN⟩, hp⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨hpN, hp⟩
      exact ⟨⟨hp.pos, by omega⟩, hp⟩
  rw [he, Nat.primesBelow_card_eq_primeCounting', ← Nat.primeCounting_sub_one]
  simp

lemma primeCounting_div_tendsto_zero :
    Tendsto (fun N : ℕ => (N.primeCounting : ℝ)/(N : ℝ)) atTop (𝓝 0) := by
  have hl := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hb : Tendsto (fun N : ℕ => (Real.log 4+1)/Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hl
  apply squeeze_zero_norm' _ hb
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (1 : ℕ)] with N hN hN0
  rw [Nat.floor_natCast] at hN
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (div_le_div_of_nonneg_right hN (Nat.cast_nonneg N)).trans_eq
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN0)
  field_simp

noncomputable def smoothOverlap (t : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, min (smoothMangoldt t n) (Λ n)

lemma smoothOverlap_nonneg {t : ℝ} (ht : 0 < t) (N : ℕ) : 0 ≤ smoothOverlap t N := by
  exact sum_nonneg (fun n _ => le_min (smoothMangoldt_nonneg ht n) vonMangoldt_nonneg)

lemma smoothOverlap_bound {t : ℝ} (ht : 0 < t) (N : ℕ) :
    smoothOverlap t N ≤ (N.primeCounting : ℝ)/t + (Chebyshev.psi N-Chebyshev.theta N) := by
  classical
  have hp (n : ℕ) : min (smoothMangoldt t n) (Λ n) ≤
      (if n.Prime then 1/t else 0) + (if ¬ n.Prime then Λ n else 0) := by
    by_cases hn : n.Prime
    · simp only [hn, if_true, not_true_eq_false, if_false, add_zero]
      exact (min_le_left _ _).trans (smoothMangoldt_le_inv ht n)
    · simpa only [hn, if_false, not_false_eq_true, if_true, zero_add] using
        (min_le_right (smoothMangoldt t n) (Λ n))
  apply (sum_le_sum (fun n (_ : n ∈ Ioc 0 N) => hp n)).trans_eq
  rw [sum_add_distrib]
  congr 1
  · rw [← sum_filter, sum_const, nsmul_eq_mul, prime_card_eq]
    ring
  · rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, sum_filter]

lemma smoothOverlap_mean_tendsto_zero {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => smoothOverlap t N/(N : ℝ)) atTop (𝓝 0) := by
  have hh := (primeCounting_div_tendsto_zero.div_const t).add
    (psi_sub_theta_div_tendsto.comp tendsto_natCast_atTop_atTop)
  simp only [zero_div, zero_add, Function.comp_apply] at hh
  apply squeeze_zero_norm' _ hh
  filter_upwards with N
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (smoothOverlap_nonneg ht N) (Nat.cast_nonneg N))]
  apply (div_le_div_of_nonneg_right (smoothOverlap_bound ht N) (Nat.cast_nonneg N)).trans_eq
  ring

noncomputable def smoothL1Error (t : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, |smoothMangoldt t n-Λ n|

lemma smoothL1Error_identity (t : ℝ) (N : ℕ) :
    smoothL1Error t N = (∑ n ∈ Ioc 0 N, smoothMangoldt t n) +
      Chebyshev.psi N - 2*smoothOverlap t N := by
  have he (a b : ℝ) : |a-b| = a+b-2*min a b := by
    rcases le_total a b with hab | hba
    · rw [min_eq_left hab, abs_of_nonpos (sub_nonpos.mpr hab)]; ring
    · rw [min_eq_right hba, abs_of_nonneg (sub_nonneg.mpr hba)]; ring
  simp only [smoothL1Error, he, sum_sub_distrib, sum_add_distrib, ← mul_sum,
    Chebyshev.psi, Nat.floor_natCast, smoothOverlap]

/-- Exact normalized L1 discrepancy for every fixed t>0. -/
theorem smoothL1Error_mean_tendsto {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => smoothL1Error t N/(N : ℝ)) atTop
      (𝓝 (dampedMean t/t+1)) := by
  have hh := ((smoothMangoldt_mean_tendsto ht).add
    (psi_div_self_tendsto.comp tendsto_natCast_atTop_atTop)).sub
      ((smoothOverlap_mean_tendsto_zero ht).const_mul 2)
  simpa only [smoothL1Error_identity, sub_div, add_div, mul_div_assoc, mul_zero, sub_zero] using hh

/-- In the opposite order of limits, every finite-window error tends to
zero. No mean-value limit at infinity is used in this statement. -/
theorem smoothL1Error_fixed_tendsto_zero (N : ℕ) :
    Tendsto (fun t : ℝ => smoothL1Error t N) (𝓝[>] 0) (𝓝 0) := by
  have hh := tendsto_finset_sum (Ioc 0 N) (fun n _ =>
    ((smoothMangoldt_tendsto n).sub_const (Λ n)).abs)
  simpa only [sub_self, abs_zero, sum_const_zero, smoothL1Error] using hh

/-- The normalized mean discrepancy tends to TWO when the input-cutoff
limit is taken first. This is an actual error limit, not an upper budget. -/
theorem smoothL1Error_iterated_mean_tendsto_two :
    Tendsto (fun t : ℝ => dampedMean t/t+1) (𝓝[>] 0) (𝓝 2) := by
  convert dampedMean_div_tendsto_one.add_const 1 using 1; norm_num

#print axioms smoothL1Error_mean_tendsto
#print axioms smoothL1Error_fixed_tendsto_zero
#print axioms smoothL1Error_iterated_mean_tendsto_two

lemma dampedMean_div_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ dampedMean t/t := by
  apply ge_of_tendsto (smoothMangoldt_mean_tendsto ht)
  exact Eventually.of_forall (fun N => div_nonneg
    (sum_nonneg (fun n _ => smoothMangoldt_nonneg ht n)) (Nat.cast_nonneg N))

/-- At every fixed t>0, large cutoffs violate even the normalized L1
error bound one half. -/
theorem exists_large_smoothL1Error {t : ℝ} (ht : 0 < t) (B : ℕ) :
    ∃ N : ℕ, B < N ∧ (N : ℝ)/2 < smoothL1Error t N := by
  have hl : (1/2 : ℝ) < dampedMean t/t+1 := by
    linarith only [dampedMean_div_nonneg ht]
  obtain ⟨N, hN, hB, hN0⟩ := (((tendsto_order.mp (smoothL1Error_mean_tendsto ht)).1 (1/2) hl).and
    ((eventually_gt_atTop B).and (eventually_ge_atTop (1 : ℕ)))).exists
  refine ⟨N, hB, ?_⟩
  have hh := (lt_div_iff₀ (Nat.cast_pos.mpr hN0)).mp hN
  linarith only [hh]

/-- Explicit failure of the proposed uniform-in-N absolute-error limit. -/
theorem not_uniform_smoothL1_approximation :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ∀ N : ℕ, smoothL1Error t N ≤ ε*N) := by
  intro h
  obtain ⟨δ, hδ, hbound⟩ := h (1/2) (by norm_num)
  have ht : 0 < δ/2 := by positivity
  obtain ⟨N, _, hN⟩ := exists_large_smoothL1Error ht 0
  have hh := hbound (δ/2) ht (by linarith) N
  linarith only [hN, hh]

#print axioms exists_large_smoothL1Error
#print axioms not_uniform_smoothL1_approximation

end Erdos972FullSmoothL1Obstruction
