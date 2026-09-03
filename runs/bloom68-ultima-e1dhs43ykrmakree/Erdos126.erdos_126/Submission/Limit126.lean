import FormalConjecturesUtil
import Submission.Independent126

/-!
# Polynomial bounds and the extremal logarithmic limit for problem 126

The analytic theorem applies to any natural-valued function satisfying the displayed
polynomial bound; no monotonicity hypothesis is needed. The finite-set transfer below
is conditional on a cardinality bound for sets of positive natural numbers.
-/

namespace E126

open Filter Topology

/-- A polynomial upper bound for the argument forces growth faster than its logarithm. -/
theorem polynomial_bound_tendsto (f : ℕ → ℕ)
    (h : ∀ n, n ≤ 1024 * (f n + 1) ^ 8 + 1) :
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log (n : ℝ)) atTop atTop := by
  have hf : Tendsto f atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_gt_atTop (1024 * (b + 1) ^ 8 + 1)] with n hn
    by_contra hbf
    have hfb : f n ≤ b := by omega
    have hbound : 1024 * (f n + 1) ^ 8 + 1 ≤ 1024 * (b + 1) ^ 8 + 1 := by
      gcongr
    exact (not_lt_of_ge ((h n).trans hbound)) hn
  have hfR : Tendsto (fun n => (f n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hf
  have hfadd : Tendsto (fun n => (f n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 hfR
  have hsmall : Tendsto (fun n => Real.log ((f n : ℝ) + 1) / (f n : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_neg_cancel_right] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hfadd
  have hmajorant : Tendsto
      (fun n => (Real.log 2048 + 8 * Real.log ((f n : ℝ) + 1)) / (f n : ℝ))
      atTop (𝓝 0) := by
    simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using
      (hfR.const_div_atTop (Real.log 2048)).add (hsmall.const_mul 8)
  have hlog : ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ≤ Real.log 2048 + 8 * Real.log ((f n : ℝ) + 1) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hreal : (n : ℝ) ≤ 1024 * ((f n : ℝ) + 1) ^ 8 + 1 := by
      exact_mod_cast h n
    have hp : (1 : ℝ) ≤ ((f n : ℝ) + 1) ^ 8 :=
      one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg _))
    have hupper : (n : ℝ) ≤ 2048 * ((f n : ℝ) + 1) ^ 8 := by
      linarith only [hreal, hp]
    calc
      Real.log (n : ℝ) ≤ Real.log (2048 * ((f n : ℝ) + 1) ^ 8) :=
        Real.log_le_log (by exact_mod_cast hn) hupper
      _ = Real.log 2048 + 8 * Real.log ((f n : ℝ) + 1) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        norm_num
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n : ℝ) / (f n : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ), hfR.eventually_gt_atTop 0] with n hn hfn
    exact div_pos (Real.log_pos (by exact_mod_cast hn)) hfn
  have hzero : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (f n : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero' (hpos.mono fun _ hn => hn.le) ?_ hmajorant
    filter_upwards [hlog] with n hn
    exact div_le_div_of_nonneg_right hn (Nat.cast_nonneg _)
  have hright : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (f n : ℝ))
      atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hzero, hpos⟩
  simpa only [Function.comp_def, inv_div] using tendsto_inv_nhdsGT_zero.comp hright

/-- A bound for positive sets extends to all natural sets with an additive cost of one. -/
theorem card_bound_of_positive_bound
    (hpos : ∀ (A : Finset ℕ), (∀ a ∈ A, 0 < a) →
      A.card ≤ 1024 * ((∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card + 1) ^ 8)
    (A : Finset ℕ) :
    A.card ≤ 1024 * ((∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card + 1) ^ 8 + 1 := by
  have hB := hpos (A.erase 0) (by
    intro a ha
    exact Nat.pos_of_ne_zero (Finset.mem_erase.mp ha).1)
  change (A.erase 0).card ≤ 1024 * (Independent126.factorCount (A.erase 0) + 1) ^ 8 at hB
  have hmono := Independent126.factorCount_mono (Finset.erase_subset 0 A)
  have hbound : 1024 * (Independent126.factorCount (A.erase 0) + 1) ^ 8 ≤
      1024 * (Independent126.factorCount A + 1) ^ 8 := by
    gcongr
  have hcard : A.card - 1 ≤ (A.erase 0).card := Finset.pred_card_le_card_erase
  change A.card ≤ 1024 * (Independent126.factorCount A + 1) ^ 8 + 1
  omega

/-- An attained extremal minimum inherits the polynomial bound, including the zero correction. -/
theorem maximal_polynomial_bound {f : ℕ → ℕ}
    (hf : Independent126.IsMaximalAddFactorsCard f)
    (hpos : ∀ (A : Finset ℕ), (∀ a ∈ A, 0 < a) →
      A.card ≤ 1024 * ((∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card + 1) ^ 8) :
    ∀ n, n ≤ 1024 * (f n + 1) ^ 8 + 1 := by
  intro n
  obtain ⟨A, hA, hcost⟩ := Independent126.maximal_attained hf n
  have h := card_bound_of_positive_bound hpos A
  change A.card ≤ 1024 * (Independent126.factorCount A + 1) ^ 8 + 1 at h
  simpa only [hA, hcost] using h

/-- Conditional transfer from the positive-set cardinality bound to the extremal logarithmic limit. -/
theorem maximal_tendsto_of_positive_bound {f : ℕ → ℕ}
    (hf : Independent126.IsMaximalAddFactorsCard f)
    (hpos : ∀ (A : Finset ℕ), (∀ a ∈ A, 0 < a) →
      A.card ≤ 1024 * ((∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card + 1) ^ 8) :
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log (n : ℝ)) atTop atTop :=
  polynomial_bound_tendsto f (maximal_polynomial_bound hf hpos)

#print axioms polynomial_bound_tendsto
#print axioms card_bound_of_positive_bound
#print axioms maximal_polynomial_bound
#print axioms maximal_tendsto_of_positive_bound

end E126
