import Submission.SievePolynomial

/-! A sharper, one-sided error bound for arbitrary finite sieve polynomials. -/
namespace Erdos970.BlockSieve.SievePolynomial
open Erdos970.BrunCriterion

/-- Positive coefficients can lose at most their expected count, or one if that is smaller. -/
noncomputable def lowerCost (S : SievePolynomial) (m : ℕ) : ℝ :=
  ∑ a : S.Term, (max (S.coefficient a) 0 *
    min 1 ((m : ℝ) / ∏ p ∈ S.primes a, (p : ℝ)) + max (-S.coefficient a) 0)

theorem lowerCost_nonneg (S : SievePolynomial) (m : ℕ) : 0 ≤ S.lowerCost m := by
  apply Finset.sum_nonneg
  intro a ha
  exact add_nonneg (mul_nonneg (le_max_right _ _) (le_min (by norm_num) (by positivity)))
    (le_max_right _ _)

theorem lowerCost_le_cost (S : SievePolynomial) (m : ℕ) : S.lowerCost m ≤ S.cost := by
  apply Finset.sum_le_sum
  intro a ha
  have hh := mul_le_mul_of_nonneg_left
    (min_le_left 1 ((m : ℝ) / ∏ p ∈ S.primes a, (p : ℝ)))
    (le_max_right (S.coefficient a) 0)
  by_cases hc : 0 ≤ S.coefficient a
  · rw [max_eq_left hc, max_eq_right (by linarith), abs_of_nonneg hc, add_zero]
    simpa only [max_eq_left hc, mul_one] using hh
  · have hc' : S.coefficient a ≤ 0 := by linarith
    simp only [max_eq_right hc', max_eq_left (neg_nonneg.mpr hc'),
      abs_of_nonpos hc', zero_mul, zero_add, le_refl]

/-- The elementary one-sided error estimate, independent of any sieve construction. -/
theorem coefficient_error_le (c E N : ℝ) (hN : 0 ≤ N) (herror : |N - E| ≤ 1) :
    c * E - c * N ≤ max c 0 * min 1 E + max (-c) 0 := by
  obtain ⟨hl, hu⟩ := abs_le.mp herror
  by_cases hc : 0 ≤ c
  · rw [max_eq_left hc, max_eq_right (by linarith), add_zero]
    have hsmall : E - N ≤ min 1 E := le_min (by linarith) (by linarith)
    have hh := mul_le_mul_of_nonneg_left hsmall hc
    nlinarith only [hh]
  · have hc' : c ≤ 0 := by linarith
    rw [max_eq_right hc', max_eq_left (neg_nonneg.mpr hc'), zero_mul, zero_add]
    have hh := mul_le_mul_of_nonneg_left hu (neg_nonneg.mpr hc')
    nlinarith only [hh]

/-- Unlike the absolute-error bound, this retains savings from sparse positive terms. -/
theorem interval_lower_error (S : SievePolynomial)
    (hS : ∀ a, ∀ p ∈ S.primes a, p.Prime) (r : ℕ → ℕ) (m : ℕ) :
    (m : ℝ) * S.mean - (∑ i ∈ Finset.range m, S.value r i) ≤ S.lowerCost m := by
  classical
  let C (a : S.Term) := ((Finset.range m).filter
    (fun i => ∀ p ∈ S.primes a, i ≡ r p [MOD p])).card
  have hcount : (∑ i ∈ Finset.range m, S.value r i) =
      ∑ a : S.Term, S.coefficient a * C a := by
    simp only [value]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.mul_sum]
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, C]
  have hmain : (m : ℝ) * S.mean = ∑ a : S.Term,
      S.coefficient a * ((m : ℝ) / ∏ p ∈ S.primes a, (p : ℝ)) := by
    rw [mean, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [hmain, hcount, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro a ha
  exact coefficient_error_le _ _ _ (Nat.cast_nonneg _)
    (intersection_count_error (S.primes a) (hS a) r m)

/-- A lower sieve weight that is nonpositive throughout an interval yields this improved test. -/
theorem cover_mean_le_lowerCost (S : SievePolynomial)
    (hS : ∀ a, ∀ p ∈ S.primes a, p.Prime) (r : ℕ → ℕ) (m : ℕ)
    (hpoint : ∀ i < m, S.value r i ≤ 0) :
    (m : ℝ) * S.mean ≤ S.lowerCost m := by
  have hh := interval_lower_error S hS r m
  have hs : (∑ i ∈ Finset.range m, S.value r i) ≤ 0 :=
    Finset.sum_nonpos (fun i hi => hpoint i (Finset.mem_range.mp hi))
  linarith

#print axioms interval_lower_error
#print axioms cover_mean_le_lowerCost
end Erdos970.BlockSieve.SievePolynomial
