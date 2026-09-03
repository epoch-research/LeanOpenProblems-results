import Submission.IndexDependentTelescoping
import Submission.FactorialTailCriterion

/-!
A rational comparison series at the quadratic boundary of the tail criterion.
This is NOT the coefficient sequence of Erdős 68, and is not a disproof of
that conjecture.
-/

namespace QuadraticTailComparison

open Filter Topology

def tail (n : ℕ) : ℤ :=
  if n % 2 = 0 then (n : ℤ) - 3 else (n : ℤ) * ((n : ℤ) - 4) - 1

def coeff (n : ℕ) : ℤ :=
  if n < 5 then 0 else (n : ℤ) * tail (n - 1) - tail n

lemma coeff_odd (n : ℕ) (hn : 5 ≤ n) (ho : n % 2 = 1) : coeff n = 1 := by
  have he : (n - 1) % 2 = 0 := by omega
  simp only [coeff, if_neg (by omega : ¬n < 5), tail, he, if_true,
    if_neg (by omega : ¬n % 2 = 0)]
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  push_cast
  ring

lemma coeff_even (n : ℕ) (hn : 5 ≤ n) (he : n % 2 = 0) :
    coeff n = ((n : ℤ) - 1) * ((n : ℤ) * ((n : ℤ) - 5) - 2) + 1 := by
  have ho : ¬(n - 1) % 2 = 0 := by omega
  simp only [coeff, if_neg (by omega : ¬n < 5), tail, ho, if_false, he, if_true]
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  push_cast
  ring

lemma coeff_nonneg (n : ℕ) : 0 ≤ coeff n := by
  by_cases hn : n < 5
  · simp [coeff, hn]
  · have hn' : 5 ≤ n := by omega
    rcases Nat.mod_two_eq_zero_or_one n with he | ho
    · rw [coeff_even n hn' he]
      have hn6 : (6 : ℤ) ≤ n := by exact_mod_cast (show 6 ≤ n by omega)
      have hm : (0 : ℤ) ≤ (n : ℤ) * ((n : ℤ) - 5) - 2 := by nlinarith
      have hp := mul_nonneg (show (0 : ℤ) ≤ (n : ℤ) - 1 by omega) hm
      omega
    · rw [coeff_odd n hn' ho]
      omega

lemma coeff_congruence (n : ℕ) (hn : 4 ≤ n) :
    (n : ℤ) ∣ coeff (n + 1) - 1 := by
  rcases Nat.mod_two_eq_zero_or_one (n + 1) with he | ho
  · rw [coeff_even (n + 1) (by omega) he]
    refine ⟨(n + 1 : ℤ) * ((n + 1 : ℤ) - 5) - 2, ?_⟩
    push_cast
    ring
  · rw [coeff_odd (n + 1) (by omega) ho, sub_self]
    exact dvd_zero _

lemma coeff_prime (p : ℕ) (hp5 : 5 ≤ p) (hp : p.Prime) : coeff p = 1 :=
  coeff_odd p hp5 (hp.eq_two_or_odd.resolve_left (by omega))

lemma tail_bounds (n : ℕ) (hn : 4 ≤ n) : 0 < tail n ∧ tail n ≤ (n : ℤ) ^ 2 := by
  have hn' : (4 : ℤ) ≤ n := by exact_mod_cast hn
  unfold tail
  split_ifs with he
  · constructor <;> nlinarith
  · have hn5 : (5 : ℤ) ≤ n := by exact_mod_cast (show 5 ≤ n by omega)
    constructor <;> nlinarith

noncomputable def normalizedTail (n : ℕ) : ℝ := (tail n : ℝ) / n.factorial

lemma summable_normalizedTail : Summable normalizedTail := by
  apply (IndexDependentTelescoping.summable_nat_pow_div_factorial 2).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop 4] with n hn
  have ht0 : (0 : ℝ) ≤ tail n := by exact_mod_cast (tail_bounds n hn).1.le
  have htu : (tail n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast (tail_bounds n hn).2
  dsimp [normalizedTail]
  rw [abs_of_nonneg (div_nonneg ht0 (by positivity))]
  exact div_le_div_of_nonneg_right htu (by positivity)

lemma coeff_div_succ (n : ℕ) (hn : 4 ≤ n) :
    (coeff (n + 1) : ℝ) / (n + 1).factorial = normalizedTail n - normalizedTail (n + 1) := by
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn0 : (n + 1 : ℝ) ≠ 0 := by positivity
  simp only [coeff, if_neg (by omega : ¬n + 1 < 5), Nat.add_sub_cancel,
    normalizedTail, Nat.factorial_succ]
  push_cast
  field_simp

lemma hasSum_shifted_coeff :
    HasSum (fun n : ℕ => (coeff (n + 5) : ℝ) / (n + 5).factorial) (1 / 24 : ℝ) := by
  have hs4 : Summable (fun n => normalizedTail (n + 4)) :=
    (summable_nat_add_iff 4).mpr summable_normalizedTail
  have hs5 : Summable (fun n => normalizedTail (n + 5)) :=
    (summable_nat_add_iff 5).mpr summable_normalizedTail
  have he := hs4.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, zero_add, Nat.add_assoc] at he
  have hb : normalizedTail 4 = (1 / 24 : ℝ) := by norm_num [normalizedTail, tail]
  rw [hb] at he
  have he' : (∑' n : ℕ, normalizedTail (n + 4)) -
      (∑' n : ℕ, normalizedTail (n + 5)) = (1 / 24 : ℝ) := by linarith
  have hh := hs4.hasSum.sub hs5.hasSum
  rw [he'] at hh
  convert hh using 1
  funext n
  simpa only [Nat.add_assoc] using coeff_div_succ (n + 4) (by omega)

lemma prefix_zero : (∑ k ∈ Finset.range 5, (coeff k : ℝ) / k.factorial) = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  simp [coeff, Finset.mem_range.mp hk]

lemma summable_coeff : Summable (fun n : ℕ => (coeff n : ℝ) / n.factorial) :=
  (summable_nat_add_iff 5).mp hasSum_shifted_coeff.summable

/-- This different series sums to the rational number 1/24. -/
theorem sum_coeff : (∑' n : ℕ, (coeff n : ℝ) / n.factorial) = (1 / 24 : ℝ) := by
  have he := summable_coeff.sum_add_tsum_nat_add 5
  rw [prefix_zero, zero_add, hasSum_shifted_coeff.tsum_eq] at he
  exact he.symm

lemma prefix_identity (n : ℕ) (hn : 4 ≤ n) :
    (∑ k ∈ Finset.range (n + 1), (coeff k : ℝ) / k.factorial) =
      (1 / 24 : ℝ) - normalizedTail n := by
  induction n, hn using Nat.le_induction with
  | base => rw [prefix_zero]; norm_num [normalizedTail, tail]
  | succ n hn ih =>
      rw [Finset.sum_range_succ, ih, coeff_div_succ n hn]
      ring

lemma scaledTail_eq (n : ℕ) (hn : 4 ≤ n) :
    FactorialTailCriterion.scaledTail coeff n = (tail n : ℝ) := by
  unfold FactorialTailCriterion.scaledTail
  rw [sum_coeff, prefix_identity n hn]
  simp only [sub_sub_cancel, normalizedTail]
  exact mul_div_cancel₀ _ (by positivity)

/-- All coefficients are nonnegative; prime coefficients and predecessor
congruences hold eventually; the tails are positive and at most n². Yet the
sum is rational, so an unrestricted quadratic version of the criterion would
be false. This is not a claim about the original coefficients in Spec.lean. -/
theorem comparison_properties :
    (∀ n : ℕ, 0 ≤ coeff n) ∧
    (∀ n : ℕ, 4 ≤ n → (n : ℤ) ∣ coeff (n + 1) - 1) ∧
    (∀ p : ℕ, 5 ≤ p → p.Prime → coeff p = 1) ∧
    (∀ n : ℕ, 4 ≤ n → 0 < FactorialTailCriterion.scaledTail coeff n ∧
      FactorialTailCriterion.scaledTail coeff n ≤ (n : ℝ) ^ 2) ∧
    (∑' n : ℕ, (coeff n : ℝ) / n.factorial) = (1 / 24 : ℝ) := by
  refine ⟨coeff_nonneg, coeff_congruence, coeff_prime, ?_, sum_coeff⟩
  intro n hn
  rw [scaledTail_eq n hn]
  exact_mod_cast tail_bounds n hn

#print axioms sum_coeff
#print axioms comparison_properties

end QuadraticTailComparison
