import Submission.Certificates

/-!
# A finite large-prime tail bound for Carmichael numbers

The Carmichael numbers `n ≤ X` with a prime divisor `p > y` form the union,
over primes in `(y, X]`, of the fixed-prime sets from `Submission.Certificates`.
Their cardinality is bounded by the sum of the fixed-prime certificates.
After passing to real numbers and discarding the primality restriction, the
reciprocal weights telescope:

`∑_{y < j ≤ X} 1 / (j * (j - 1)) = 1 / y - 1 / X` when `1 ≤ y ≤ X`.

Thus the large-prime tail has cardinality at most `(X : ℝ) / (y : ℝ)` for
`1 ≤ y`. The final bound allows every natural `X`, including `0`; empty
intervals are treated separately in the reciprocal-sum bound. This is a
finite counting estimate, not an asymptotic density proof. Only the verified
certificate module is imported, not a counting or density target.
-/

open scoped BigOperators

namespace Erdos1057.CarmichaelPrimeTail

open CarmichaelCertificates

/-- Carmichael numbers at most `X` with a prime divisor strictly greater than `y`. -/
noncomputable def carmichaelsWithLargePrimeFactorUpTo (y X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (X + 1)).filter
    (fun n => IsCarmichael n ∧ ∃ p : ℕ, p.Prime ∧ y < p ∧ p ∣ n)

@[simp]
theorem mem_carmichaelsWithLargePrimeFactorUpTo {y X n : ℕ} :
    n ∈ carmichaelsWithLargePrimeFactorUpTo y X ↔
      n ≤ X ∧ IsCarmichael n ∧ ∃ p : ℕ, p.Prime ∧ y < p ∧ p ∣ n := by
  classical
  simp only [carmichaelsWithLargePrimeFactorUpTo, Finset.mem_filter,
    Finset.mem_range_succ_iff]

/-- The finset represents exactly the bounded large-prime tail. -/
theorem coe_carmichaelsWithLargePrimeFactorUpTo (y X : ℕ) :
    (carmichaelsWithLargePrimeFactorUpTo y X : Set ℕ) =
      {n : ℕ | n ≤ X ∧ IsCarmichael n ∧ ∃ p : ℕ, p.Prime ∧ y < p ∧ p ∣ n} := by
  ext n
  exact mem_carmichaelsWithLargePrimeFactorUpTo

/-- Finiteness does not require positivity of either cutoff. -/
theorem carmichaels_with_large_prime_factor_finite (y X : ℕ) :
    {n : ℕ | n ≤ X ∧ IsCarmichael n ∧ ∃ p : ℕ, p.Prime ∧ y < p ∧ p ∣ n}.Finite := by
  rw [← coe_carmichaelsWithLargePrimeFactorUpTo y X]
  exact Finset.finite_toSet _

/-- Every prime divisor is at most the positive Carmichael number it divides,
so only primes in `(y, X]` are needed in the union. -/
theorem carmichaelsWithLargePrimeFactorUpTo_eq_biUnion (y X : ℕ) :
    carmichaelsWithLargePrimeFactorUpTo y X =
      ((Finset.Ioc y X).filter Nat.Prime).biUnion
        (fun p => carmichaelsWithPrimeFactorUpTo p X) := by
  classical
  ext n
  simp only [mem_carmichaelsWithLargePrimeFactorUpTo, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_Ioc, mem_carmichaelsWithPrimeFactorUpTo]
  constructor
  · rintro ⟨hnX, hn, p, hp, hyp, hpn⟩
    have hpX : p ≤ X :=
      (Nat.le_of_dvd (divisor_pos hn (dvd_refl n)) hpn).trans hnX
    exact ⟨p, ⟨⟨hyp, hpX⟩, hp⟩, hnX, hn, hpn⟩
  · rintro ⟨p, ⟨⟨hyp, _⟩, hp⟩, hnX, hn, hpn⟩
    exact ⟨hnX, hn, p, hp, hyp, hpn⟩

/-- The finite union bound, using the exact natural-number certificate for each prime. -/
theorem card_carmichaelsWithLargePrimeFactorUpTo_le_sum (y X : ℕ) :
    (carmichaelsWithLargePrimeFactorUpTo y X).card ≤
      ∑ p ∈ (Finset.Ioc y X).filter Nat.Prime, X / (p * (p - 1)) := by
  classical
  rw [carmichaelsWithLargePrimeFactorUpTo_eq_biUnion]
  exact Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun p hp =>
    card_carmichaelsWithPrimeFactorUpTo_le (Finset.mem_filter.mp hp).2 X))

/-- The reciprocal weights telescope exactly when `1 ≤ y ≤ X`, including the
empty interval `y = X`. The predecessor in the denominator is natural subtraction. -/
theorem sum_Ioc_recip_mul_pred {y X : ℕ} (hy : 1 ≤ y) (hyX : y ≤ X) :
    (∑ j ∈ Finset.Ioc y X, (1 : ℝ) / ((j : ℝ) * ((j - 1 : ℕ) : ℝ))) =
      1 / (y : ℝ) - 1 / (X : ℝ) := by
  induction X, hyX using Nat.le_induction with
  | base => simp
  | succ X hyX ih =>
    rw [Finset.sum_Ioc_succ_top hyX, ih]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    have hX : (X : ℝ) ≠ 0 := by
      have : 0 < X := by omega
      exact_mod_cast Nat.ne_of_gt this
    have hX1 : (X : ℝ) + 1 ≠ 0 := by positivity
    have hstep : (1 : ℝ) / (((X : ℝ) + 1) * (X : ℝ)) =
        1 / (X : ℝ) - 1 / ((X : ℝ) + 1) := by
      field_simp
      ring
    rw [hstep]
    ring

/-- The reciprocal tail bound, also valid when `X < y` and the interval is empty. -/
theorem sum_Ioc_recip_mul_pred_le {y : ℕ} (hy : 1 ≤ y) (X : ℕ) :
    (∑ j ∈ Finset.Ioc y X, (1 : ℝ) / ((j : ℝ) * ((j - 1 : ℕ) : ℝ))) ≤
      1 / (y : ℝ) := by
  by_cases hyX : y ≤ X
  · rw [sum_Ioc_recip_mul_pred hy hyX]
    exact sub_le_self _ (by positivity)
  · rw [Finset.Ioc_eq_empty_of_le (show X ≤ y by omega), Finset.sum_empty]
    positivity

/-- Restricting the nonnegative reciprocal weights to primes only decreases the sum. -/
theorem sum_primes_Ioc_recip_mul_pred_le {y : ℕ} (hy : 1 ≤ y) (X : ℕ) :
    (∑ p ∈ (Finset.Ioc y X).filter Nat.Prime,
      (1 : ℝ) / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))) ≤ 1 / (y : ℝ) := by
  classical
  calc
    _ ≤ ∑ j ∈ Finset.Ioc y X, (1 : ℝ) / ((j : ℝ) * ((j - 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro j _ _
      positivity
    _ ≤ 1 / (y : ℝ) := sum_Ioc_recip_mul_pred_le hy X

/-- The finite large-prime tail bound, with real division and no rounding error.
No positivity assumption on `X` is necessary. -/
theorem card_carmichaelsWithLargePrimeFactorUpTo_le_real {y : ℕ}
    (hy : 1 ≤ y) (X : ℕ) :
    ((carmichaelsWithLargePrimeFactorUpTo y X).card : ℝ) ≤ (X : ℝ) / (y : ℝ) := by
  classical
  calc
    ((carmichaelsWithLargePrimeFactorUpTo y X).card : ℝ) ≤
        ((∑ p ∈ (Finset.Ioc y X).filter Nat.Prime,
          X / (p * (p - 1)) : ℕ) : ℝ) := by
      exact_mod_cast card_carmichaelsWithLargePrimeFactorUpTo_le_sum y X
    _ = ∑ p ∈ (Finset.Ioc y X).filter Nat.Prime,
        ((X / (p * (p - 1)) : ℕ) : ℝ) := by rw [Nat.cast_sum]
    _ ≤ ∑ p ∈ (Finset.Ioc y X).filter Nat.Prime,
        (X : ℝ) / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro p _
      simpa only [Nat.cast_mul] using
        (Nat.cast_div_le (α := ℝ) (m := X) (n := p * (p - 1)))
    _ = (X : ℝ) * (∑ p ∈ (Finset.Ioc y X).filter Nat.Prime,
        (1 : ℝ) / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))) := by
      simp only [Finset.mul_sum, div_eq_mul_inv, one_mul]
    _ ≤ (X : ℝ) * (1 / (y : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_primes_Ioc_recip_mul_pred_le hy X) (Nat.cast_nonneg X)
    _ = (X : ℝ) / (y : ℝ) := by simp only [div_eq_mul_inv, one_mul]

/-- The large-prime tail bound stated directly for the cardinality of a set of naturals. -/
theorem ncard_carmichaels_with_large_prime_factor_le_real {y : ℕ}
    (hy : 1 ≤ y) (X : ℕ) :
    ({n : ℕ | n ≤ X ∧ IsCarmichael n ∧
      ∃ p : ℕ, p.Prime ∧ y < p ∧ p ∣ n}.ncard : ℝ) ≤ (X : ℝ) / (y : ℝ) := by
  rw [← coe_carmichaelsWithLargePrimeFactorUpTo y X, Set.ncard_coe_finset]
  exact card_carmichaelsWithLargePrimeFactorUpTo_le_real hy X

end Erdos1057.CarmichaelPrimeTail
