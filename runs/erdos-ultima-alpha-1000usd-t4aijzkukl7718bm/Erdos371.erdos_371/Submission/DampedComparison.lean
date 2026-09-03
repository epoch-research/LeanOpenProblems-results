import Submission.DampedAlladi
import Submission.SmoothedComparison

/-! A uniformly bounded damped comparison and its quantitative approximation
to the actual sign. Signed cancellation of the damped comparison is not assumed
unconditionally. -/
namespace Erdos371
open Finset Filter
open scoped Topology

noncomputable def dampedFactorSign (t : ℝ) (n : ℕ) : ℝ :=
  dampedColour t (fun p => if p ∣ n+1 then 1 else -1) (n*(n+1)).primeFactors

lemma dampedFactorSign_abs_le_one (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) :
    |dampedFactorSign t n| ≤ 1 := by
  apply dampedColour_abs_le_one t ht ht1
  intro p hp
  split_ifs <;> norm_num

lemma dampedFactorSign_one (n : ℕ) (hn : 1 < n) : dampedFactorSign 1 n=factorSign n := by
  simpa only [dampedFactorSign,dampedColour,one_pow,one_mul,factorSign] using
    (comparison_as_subset_sum n hn).symm

lemma dampedFactorSign_point_error (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) (hn : 1 < n) :
    |dampedFactorSign t n-factorSign n| ≤ 2*(1-t) := by
  have hP : (n*(n+1)).primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by nlinarith)
  rw [← dampedFactorSign_one n hn]
  unfold dampedFactorSign
  rw [dampedColour_one _ _ hP]
  apply dampedColour_max_error t ht ht1
  intro p hp
  split_ifs <;> norm_num

/-- The exceptional initial two inputs cost at most 4/N. The other error
bound is uniform in N and in the number of prime factors. -/
theorem dampedFactorSign_mean_error_bound (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ range N, |dampedFactorSign t n-factorSign n|)/N ≤ 2*(1-t)+4/(N : ℝ) := by
  have hp (n : ℕ) : |dampedFactorSign t n-factorSign n| ≤
      2*(1-t)+(if n < 2 then (2 : ℝ) else 0) := by
    by_cases hn : n < 2
    · rw [if_pos hn]
      have hS : |factorSign n|=1 := by simp only [factorSign,predicateSign]; split_ifs <;> norm_num
      have hh := (abs_sub _ _).trans (add_le_add (dampedFactorSign_abs_le_one t ht ht1 n) (le_of_eq hS))
      linarith
    · rw [if_neg hn,add_zero]
      exact dampedFactorSign_point_error t ht ht1 n (by omega)
  have hi : (∑ n ∈ range N, if n < 2 then (2 : ℝ) else 0) ≤ 4 := by
    rw [← sum_filter,sum_const,nsmul_eq_mul]
    have hc : ((range N).filter (fun n => n < 2)).card ≤ 2 := by
      apply (card_le_card _).trans_eq (card_range 2)
      intro n hn
      exact mem_range.mpr (mem_filter.mp hn).2
    have hcR : (((range N).filter (fun n => n < 2)).card : ℝ) ≤ 2 := by exact_mod_cast hc
    linarith
  have hs := sum_le_sum (s := range N) (fun n hn => hp n)
  rw [sum_add_distrib,sum_const,card_range,nsmul_eq_mul] at hs
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  apply le_trans (div_le_div_of_nonneg_right (hs.trans (add_le_add le_rfl hi)) hNR.le)
  rw [add_div,mul_div_cancel_left₀ _ hNR.ne']

/-- This is a sufficient arithmetic route, not an assertion that any of
its damped mean hypotheses are available. Damping parameters approach 1
only AFTER the fixed-parameter limits have been proved. -/
theorem density_of_damped_cancellation (t : ℕ → ℝ)
    (ht : ∀ k, 0 ≤ t k ∧ t k ≤ 1) (htlim : Tendsto t atTop (𝓝 1))
    (hcancel : ∀ k, Tendsto (fun N : ℕ => (∑ n ∈ range N, dampedFactorSign (t k) n)/N)
      atTop (𝓝 0)) :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) := by
  rw [density_iff_signed_count]
  simp_rw [← factorSign_sum_eq_count_difference]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have herror : Tendsto (fun k => 2*(1-t k)) atTop (𝓝 0) := by
    simpa only [sub_self,mul_zero] using ((tendsto_const_nhds (x := (1 : ℝ))).sub htlim).const_mul 2
  obtain ⟨k,hk⟩ := (herror.eventually_lt_const (show (0 : ℝ) < ε/3 by positivity)).exists
  have hfour : Tendsto (fun N : ℕ => (4 : ℝ)/N) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat 4
  have hmean := (hcancel k).abs
  simp only [abs_zero] at hmean
  filter_upwards [hmean.eventually_lt_const (show (0 : ℝ) < ε/3 by positivity),
    hfour.eventually_lt_const (show (0 : ℝ) < ε/3 by positivity),eventually_gt_atTop (0 : ℕ)] with N hm h4 hn
  have he := dampedFactorSign_mean_error_bound (t k) (ht k).1 (ht k).2 N hn
  have hdiff : |(∑ n ∈ range N, dampedFactorSign (t k) n)/N-(∑ n ∈ range N, factorSign n)/N| ≤
      (∑ n ∈ range N, |dampedFactorSign (t k) n-factorSign n|)/N := by
    rw [← sub_div,← sum_sub_distrib,abs_div,abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg N)
  have htri := abs_sub_le ((∑ n ∈ range N, factorSign n)/N)
    ((∑ n ∈ range N, dampedFactorSign (t k) n)/N) 0
  rw [abs_sub_comm] at hdiff
  simp only [sub_zero] at htri
  rw [Real.dist_eq,sub_zero]
  linarith

#print axioms dampedFactorSign_mean_error_bound
#print axioms density_of_damped_cancellation
end Erdos371
