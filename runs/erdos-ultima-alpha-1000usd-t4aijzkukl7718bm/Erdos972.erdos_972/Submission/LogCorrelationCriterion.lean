import Submission.SublinearCorrelationCriterion
import Submission.ReciprocalPrefixSummability

/-! The proper-prime-power contribution has finite reciprocal weight.
Unbounded reciprocal-weighted Mangoldt correlation is consequently sufficient
for prime-pair infinitude. Such unboundedness is a hypothesis, not a lower
bound established in this file. -/
namespace Erdos972LogCorrelationCriterion

open Finset Filter ArithmeticFunction
open Erdos972PrimePowerError Erdos972CorrelationVaughan Erdos972Topology
open Erdos972SublinearCorrelationCriterion Erdos972ReciprocalPrefixSummability

noncomputable def mangoldtTerm (α : ℝ) (n : ℕ) : ℝ := Λ n * Λ (floorMul α n)

noncomputable def primeTerm (α : ℝ) (n : ℕ) : ℝ := by
  classical
  exact if n.Prime ∧ (floorMul α n).Prime then
    Real.log n * Real.log (floorMul α n) else 0

noncomputable def powerErrorTerm (α : ℝ) (n : ℕ) : ℝ :=
  mangoldtTerm α n - primeTerm α n

lemma primeTerm_nonneg (α : ℝ) (n : ℕ) : 0 ≤ primeTerm α n := by
  classical
  unfold primeTerm
  split_ifs
  · exact mul_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  · exact le_rfl

lemma primeTerm_le (α : ℝ) (n : ℕ) : primeTerm α n ≤ mangoldtTerm α n := by
  classical
  unfold primeTerm mangoldtTerm
  split_ifs with h
  · rw [vonMangoldt_apply_prime h.1, vonMangoldt_apply_prime h.2]
  · exact mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg

lemma powerErrorTerm_nonneg (α : ℝ) (n : ℕ) : 0 ≤ powerErrorTerm α n :=
  sub_nonneg.mpr (primeTerm_le α n)

@[simp] lemma primeTerm_zero (α : ℝ) : primeTerm α 0 = 0 := by simp [primeTerm]
@[simp] lemma powerErrorTerm_zero (α : ℝ) : powerErrorTerm α 0 = 0 := by
  simp [powerErrorTerm, mangoldtTerm]

lemma sum_range_succ_eq_Ioc {a : ℕ → ℝ} (ha : a 0 = 0) (N : ℕ) :
    ∑ n ∈ range (N+1), a n = ∑ n ∈ Ioc 0 N, a n := by
  rw [Nat.range_eq_Icc_zero_sub_one _ (by omega), add_tsub_cancel_right,
    Icc_eq_cons_Ioc (Nat.zero_le N), sum_cons, ha, zero_add]

lemma powerErrorTerm_prefix (α : ℝ) (N : ℕ) :
    ∑ n ∈ range (N+1), powerErrorTerm α n =
      mangoldtCorrelation α N - primeCorrelation α N := by
  classical
  rw [sum_range_succ_eq_Ioc (powerErrorTerm_zero α)]
  simp only [powerErrorTerm, sum_sub_distrib, mangoldtTerm, mangoldtCorrelation,
    primeCorrelation, sum_filter, primeTerm]

/-- A uniform sublinear power bound for the nonnegative error partial sums.
The constant may depend on the slope. -/
lemma powerErrorTerm_prefix_bound {α : ℝ} (hα : 1 ≤ α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ∑ n ∈ range (N+1), powerErrorTerm α n ≤ C * ((N+1:ℕ):ℝ)^(3/4:ℝ) := by
  have hlim := primePowerBudget_div_rpow_tendsto (s := (3/4:ℝ)) hα (by norm_num)
  obtain ⟨C, hC⟩ := hlim.bddAbove_range
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro N
  by_cases hN : N = 0
  · subst N
    simp only [zero_add, range_one, sum_singleton, powerErrorTerm_zero,
      Nat.cast_one, Real.one_rpow, mul_one]
    exact le_max_right _ _
  have hN0 : (0:ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hpow : (0:ℝ) < (N:ℝ)^(3/4:ℝ) := Real.rpow_pos_of_pos hN0 _
  have hquot : primePowerBudget α N / (N:ℝ)^(3/4:ℝ) ≤ C :=
    hC (Set.mem_range_self N)
  have hbudget : primePowerBudget α N ≤ C * (N:ℝ)^(3/4:ℝ) :=
    (div_le_iff₀ hpow).mp hquot
  rw [powerErrorTerm_prefix]
  calc
    _ ≤ primePowerBudget α N :=
      (prime_power_error_bound_sharp hα (Nat.one_le_iff_ne_zero.mpr hN)).2
    _ ≤ C * (N:ℝ)^(3/4:ℝ) := hbudget
    _ ≤ max C 0 * (N:ℝ)^(3/4:ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hpow.le
    _ ≤ max C 0 * ((N+1:ℕ):ℝ)^(3/4:ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hN0.le (Nat.cast_le.mpr (Nat.le_succ N)) (by norm_num))
        (le_max_right _ _)

/-- Unlike the unweighted error envelope, the total reciprocal-weighted
proper-prime-power contribution is finite. -/
theorem summable_powerErrorTerm_div_succ {α : ℝ} (hα : 1 ≤ α) :
    Summable (fun n : ℕ => powerErrorTerm α n / ((n+1:ℕ):ℝ)) := by
  obtain ⟨C, hC, hprefix⟩ := powerErrorTerm_prefix_bound hα
  exact summable_div_succ_of_prefix_rpow (powerErrorTerm_nonneg α) hC (by norm_num) hprefix

/-- The reciprocal series for the full Mangoldt correlation and for genuine
prime pairs have exactly the same summability behavior. -/
theorem summable_mangoldt_iff_prime {α : ℝ} (hα : 1 ≤ α) :
    Summable (fun n : ℕ => mangoldtTerm α n / ((n+1:ℕ):ℝ)) ↔
      Summable (fun n : ℕ => primeTerm α n / ((n+1:ℕ):ℝ)) := by
  have he := summable_powerErrorTerm_div_succ hα
  constructor
  · intro hm
    apply (hm.sub he).congr
    intro n
    simp only [powerErrorTerm, sub_div]
    ring
  · intro hp
    apply (hp.add he).congr
    intro n
    simp only [powerErrorTerm, sub_div]
    ring

lemma summable_prime_of_finite {α : ℝ} (hfin : (primeSet α).Finite) :
    Summable (fun n : ℕ => primeTerm α n / ((n+1:ℕ):ℝ)) := by
  classical
  apply summable_of_ne_finset_zero (s := hfin.toFinset)
  intro n hn
  have hn' : ¬ (n.Prime ∧ (floorMul α n).Prime) := by
    simpa only [Set.Finite.mem_toFinset, primeSet, Set.mem_setOf_eq, floorMul] using hn
  simp [primeTerm, hn']

/-- A non-summability target which avoids subtracting a growing prime-power
budget. Non-summability is not asserted for arbitrary irrational slopes. -/
theorem infinite_primeSet_of_not_summable {α : ℝ} (hα : 1 ≤ α)
    (hnot : ¬ Summable (fun n : ℕ => mangoldtTerm α n / ((n+1:ℕ):ℝ))) :
    (primeSet α).Infinite := by
  intro hfin
  exact hnot ((summable_mangoldt_iff_prime hα).mpr (summable_prime_of_finite hfin))

noncomputable def logMangoldtCorrelation (α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, mangoldtTerm α n / ((n+1:ℕ):ℝ)

noncomputable def logPrimeCorrelation (α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, primeTerm α n / ((n+1:ℕ):ℝ)

noncomputable def logPowerErrorBudget (α : ℝ) : ℝ :=
  ∑' n : ℕ, powerErrorTerm α n / ((n+1:ℕ):ℝ)

/-- A scale-independent bound for the difference of the two reciprocal
correlations, proved using summability of the actual nonnegative error. -/
theorem logCorrelation_error_bound {α : ℝ} (hα : 1 ≤ α) (N : ℕ) :
    0 ≤ logMangoldtCorrelation α N - logPrimeCorrelation α N ∧
      logMangoldtCorrelation α N - logPrimeCorrelation α N ≤ logPowerErrorBudget α := by
  have heq : logMangoldtCorrelation α N - logPrimeCorrelation α N =
      ∑ n ∈ Ioc 0 N, powerErrorTerm α n / ((n+1:ℕ):ℝ) := by
    simp only [logMangoldtCorrelation, logPrimeCorrelation, powerErrorTerm,
      sub_div, sum_sub_distrib]
  rw [heq]
  refine ⟨sum_nonneg (fun n _ => div_nonneg (powerErrorTerm_nonneg α n) (by positivity)), ?_⟩
  exact (summable_powerErrorTerm_div_succ hα).sum_le_tsum _
    (fun n _ => div_nonneg (powerErrorTerm_nonneg α n) (by positivity))

/-- It suffices that the reciprocal correlation be unbounded, at any rate.
This does not follow from the earlier fixed-sublinear-power criterion:
the two growth claims concern different sums. The unboundedness assumption
remains a missing analytic input. -/
theorem infinite_primeSet_of_unbounded_logCorrelation {α : ℝ} (hα : 1 ≤ α)
    (hunbounded : ∀ C : ℝ, ∃ N : ℕ, C < logMangoldtCorrelation α N) :
    (primeSet α).Infinite := by
  apply infinite_primeSet_of_not_summable hα
  intro hs
  obtain ⟨N, hN⟩ := hunbounded (∑' n : ℕ, mangoldtTerm α n / ((n+1:ℕ):ℝ))
  apply (not_le_of_gt hN)
  exact hs.sum_le_tsum _ (fun n _ =>
    div_nonneg (mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg) (by positivity))

/-- A global sublinear power bound makes the reciprocal correlation bounded.
In particular the reciprocal criterion must not be advertised as weaker
than every unweighted sublinear-growth criterion. -/
theorem logCorrelation_bounded_of_power_bound {α C s : ℝ}
    (hC : 0 ≤ C) (hs : s < 1)
    (hbound : ∀ N : ℕ, mangoldtCorrelation α N ≤ C * ((N+1:ℕ):ℝ)^s) :
    BddAbove (Set.range (logMangoldtCorrelation α)) := by
  have hm0 : mangoldtTerm α 0 = 0 := by simp [mangoldtTerm]
  have hmpos (n : ℕ) : 0 ≤ mangoldtTerm α n :=
    mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg
  have hp (N : ℕ) : ∑ n ∈ range (N+1), mangoldtTerm α n ≤ C * ((N+1:ℕ):ℝ)^s := by
    rw [sum_range_succ_eq_Ioc hm0]
    exact hbound N
  have hsumm := summable_div_succ_of_prefix_rpow hmpos hC hs hp
  refine ⟨∑' n : ℕ, mangoldtTerm α n / ((n+1:ℕ):ℝ), ?_⟩
  rintro _ ⟨N, rfl⟩
  exact hsumm.sum_le_tsum _ (fun n _ => div_nonneg (hmpos n) (by positivity))

#print axioms summable_powerErrorTerm_div_succ
#print axioms summable_mangoldt_iff_prime
#print axioms logCorrelation_error_bound
#print axioms infinite_primeSet_of_unbounded_logCorrelation
#print axioms logCorrelation_bounded_of_power_bound

end Erdos972LogCorrelationCriterion
