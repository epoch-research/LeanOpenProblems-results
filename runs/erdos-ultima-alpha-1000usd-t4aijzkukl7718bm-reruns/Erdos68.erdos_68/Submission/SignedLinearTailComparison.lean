import Submission.IndexDependentTelescoping
import Submission.FactorialTailCriterion

/-!
# Negative linear tails do not imply irrationality

This is a rational comparison series, not the series in `Spec.lean`.
It has prime coefficients equal to one and the predecessor congruences,
but its tails are negative and bounded in absolute value by a linear function.
Thus carrying must retain a suitable sign, not merely a small absolute tail.
-/

namespace SignedLinearTailComparison

open Filter Topology

def tail (n : ℕ) : ℤ := if n % 2 = 0 then -2 else -2 * (n : ℤ) - 1

def coeff (n : ℕ) : ℤ :=
  if n = 0 then 0 else (n : ℤ) * tail (n - 1) - tail n

lemma coeff_odd (n : ℕ) (ho : n % 2 = 1) : coeff n = 1 := by
  have hn : n ≠ 0 := by omega
  have he : (n - 1) % 2 = 0 := by omega
  simp only [coeff, if_neg hn, tail, he, if_true,
    if_neg (by omega : ¬ n % 2 = 0)]
  ring

lemma coeff_even (n : ℕ) (hn : 0 < n) (he : n % 2 = 0) :
    coeff n = -((n : ℤ) - 1) * (2 * (n : ℤ) + 1) + 1 := by
  have ho : ¬ (n - 1) % 2 = 0 := by omega
  simp only [coeff, if_neg (by omega : n ≠ 0), tail, ho, if_false, he, if_true]
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  push_cast
  ring

lemma coeff_congruence (n : ℕ) : (n : ℤ) ∣ coeff (n + 1) - 1 := by
  rcases Nat.mod_two_eq_zero_or_one (n + 1) with he | ho
  · rw [coeff_even (n + 1) (by omega) he]
    refine ⟨-(2 * (n + 1 : ℤ) + 1), ?_⟩
    push_cast
    ring
  · rw [coeff_odd (n + 1) ho, sub_self]
    exact dvd_zero _

lemma coeff_prime (p : ℕ) (hp3 : 3 ≤ p) (hp : p.Prime) : coeff p = 1 :=
  coeff_odd p (hp.eq_two_or_odd.resolve_left (by omega))

lemma tail_bounds (n : ℕ) : -(2 * (n : ℤ) + 2) ≤ tail n ∧ tail n < 0 := by
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  unfold tail
  split_ifs <;> omega

lemma abs_tail_le (n : ℕ) : |(tail n : ℝ)| ≤ 2 * (n : ℝ) + 2 := by
  have ht := tail_bounds n
  have ht0 : (tail n : ℝ) < 0 := by exact_mod_cast ht.2
  have htl : -(2 * (n : ℝ) + 2) ≤ (tail n : ℝ) := by exact_mod_cast ht.1
  rw [abs_of_neg ht0]
  linarith

noncomputable def normalizedTail (n : ℕ) : ℝ := (tail n : ℝ) / n.factorial

lemma summable_normalizedTail : Summable normalizedTail := by
  have h0 := (IndexDependentTelescoping.summable_nat_pow_div_factorial 0).mul_left (2 : ℝ)
  have h1 := (IndexDependentTelescoping.summable_nat_pow_div_factorial 1).mul_left (2 : ℝ)
  apply (h1.add h0).of_norm_bounded
  intro n
  have hf : (0 : ℝ) ≤ n.factorial := by positivity
  simp only [normalizedTail, Real.norm_eq_abs, abs_div, abs_of_nonneg hf]
  have h := div_le_div_of_nonneg_right (abs_tail_le n) hf
  simpa only [pow_one, pow_zero, add_div, mul_div_assoc, mul_one_div] using h

lemma coeff_div_succ (n : ℕ) :
    (coeff (n + 1) : ℝ) / (n + 1).factorial = normalizedTail n - normalizedTail (n + 1) := by
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn0 : (n + 1 : ℝ) ≠ 0 := by positivity
  simp only [coeff, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel,
    normalizedTail, Nat.factorial_succ]
  push_cast
  field_simp

lemma hasSum_shifted_coeff :
    HasSum (fun n : ℕ => (coeff (n + 1) : ℝ) / (n + 1).factorial) (-2 : ℝ) := by
  have hs1 : Summable (fun n => normalizedTail (n + 1)) :=
    (summable_nat_add_iff 1).mpr summable_normalizedTail
  have he := summable_normalizedTail.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at he
  have hb : normalizedTail 0 = (-2 : ℝ) := by norm_num [normalizedTail, tail]
  rw [hb] at he
  have he' : (∑' n : ℕ, normalizedTail n) -
      (∑' n : ℕ, normalizedTail (n + 1)) = (-2 : ℝ) := by linarith
  have hh := summable_normalizedTail.hasSum.sub hs1.hasSum
  rw [he'] at hh
  convert hh using 1
  funext n
  exact coeff_div_succ n

lemma summable_coeff : Summable (fun n : ℕ => (coeff n : ℝ) / n.factorial) :=
  (summable_nat_add_iff 1).mp hasSum_shifted_coeff.summable

theorem sum_coeff : (∑' n : ℕ, (coeff n : ℝ) / n.factorial) = (-2 : ℝ) := by
  have he := summable_coeff.sum_add_tsum_nat_add 1
  have hc : coeff 0 = 0 := by simp [coeff]
  simpa only [Finset.sum_range_one, hc, Int.cast_zero, zero_div,
    zero_add, hasSum_shifted_coeff.tsum_eq] using he.symm

lemma prefix_identity (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (coeff k : ℝ) / k.factorial) =
      -2 - normalizedTail n := by
  induction n with
  | zero => norm_num [coeff, normalizedTail, tail]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, coeff_div_succ]
      ring

lemma scaledTail_eq (n : ℕ) :
    FactorialTailCriterion.scaledTail coeff n = (tail n : ℝ) := by
  unfold FactorialTailCriterion.scaledTail
  rw [sum_coeff, prefix_identity]
  simp only [sub_sub_cancel, normalizedTail]
  exact mul_div_cancel₀ _ (by positivity)

theorem comparison_properties :
    (∀ n : ℕ, (n : ℤ) ∣ coeff (n + 1) - 1) ∧
    (∀ p : ℕ, 3 ≤ p → p.Prime → coeff p = 1) ∧
    (∀ n : ℕ, FactorialTailCriterion.scaledTail coeff n < 0 ∧
      |FactorialTailCriterion.scaledTail coeff n| ≤ 2 * (n : ℝ) + 2) ∧
    (∑' n : ℕ, (coeff n : ℝ) / n.factorial) = (-2 : ℝ) := by
  refine ⟨coeff_congruence, coeff_prime, ?_, sum_coeff⟩
  intro n
  rw [scaledTail_eq]
  exact ⟨by exact_mod_cast (tail_bounds n).2, abs_tail_le n⟩

end SignedLinearTailComparison

#print axioms SignedLinearTailComparison.sum_coeff
#print axioms SignedLinearTailComparison.comparison_properties
