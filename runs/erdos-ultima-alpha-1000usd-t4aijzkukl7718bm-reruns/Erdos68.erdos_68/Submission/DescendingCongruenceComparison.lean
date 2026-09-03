import Submission.QuadraticTailComparison

/-!
The parity-based rational comparison also satisfies the full family of
least-prime-factor descending-factorial congruences. This is a different
coefficient sequence, not a proof or disproof of Erdős 68.
-/

namespace DescendingCongruenceComparison

open QuadraticTailComparison

/-- The new congruences hold for the rational comparison, not just for its
odd quadratic specialization. -/
theorem descending_congruence (n j : ℕ) (hn : 5 ≤ n) (hj : j < n.minFac) :
    ((n - 1).descFactorial j : ℤ) ∣ coeff n - 1 := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have hm : n.minFac = 2 :=
      (Nat.minFac_eq_two_iff n).mpr (Nat.dvd_of_mod_eq_zero he)
    have hj2 : j < 2 := by simpa only [hm] using hj
    interval_cases j
    · simp
    · simpa only [Nat.descFactorial_one, Nat.sub_add_cancel (by omega : 1 ≤ n)] using
        coeff_congruence (n - 1) (by omega)
  · rw [coeff_odd n hn ho, sub_self]
    exact dvd_zero _

theorem maximal_descending_congruence (n : ℕ) (hn : 5 ≤ n) :
    ((n - 1).descFactorial (n.minFac - 1) : ℤ) ∣ coeff n - 1 := by
  apply descending_congruence n (n.minFac - 1) hn
  have := Nat.minFac_pos n
  omega

/-- The earlier least-prime-factor factorial congruence holds too. -/
theorem minFac_factorial_congruence (n : ℕ) (hn : 5 ≤ n) :
    (n.minFac.factorial : ℤ) ∣ coeff n - 1 := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have hm : n.minFac = 2 :=
      (Nat.minFac_eq_two_iff n).mpr (Nat.dvd_of_mod_eq_zero he)
    rw [hm, coeff_even n hn he]
    norm_num only [Nat.factorial, Nat.cast_ofNat, add_sub_cancel_right]
    have hd : (2 : ℤ) ∣ (n : ℤ) := by
      exact_mod_cast (Nat.dvd_of_mod_eq_zero he : 2 ∣ n)
    exact dvd_mul_of_dvd_right (dvd_sub (dvd_mul_of_dvd_left hd _) (dvd_refl 2)) _
  · rw [coeff_odd n hn ho, sub_self]
    exact dvd_zero _

theorem coeff_pos (n : ℕ) (hn : 5 ≤ n) : 0 < coeff n := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · rw [coeff_even n hn he]
    have hn6 : (6 : ℤ) ≤ n := by exact_mod_cast (show 6 ≤ n by omega)
    have h : (0 : ℤ) ≤ (n : ℤ) * ((n : ℤ) - 5) - 2 := by nlinarith
    have := mul_nonneg (show (0 : ℤ) ≤ (n : ℤ) - 1 by omega) h
    omega
  · rw [coeff_odd n hn ho]
    norm_num

theorem strict_tail_bounds (n : ℕ) (hn : 4 ≤ n) :
    0 < FactorialTailCriterion.scaledTail coeff n ∧
    FactorialTailCriterion.scaledTail coeff n < (n : ℝ) ^ 2 := by
  rw [scaledTail_eq n hn]
  have hpos : 0 < tail n := (tail_bounds n hn).1
  refine ⟨by exact_mod_cast hpos, ?_⟩
  have hn' : (4 : ℤ) ≤ n := by exact_mod_cast hn
  have hlt : tail n < (n : ℤ) ^ 2 := by
    unfold tail
    split_ifs <;> nlinarith
  exact_mod_cast hlt

theorem even_tail_bound (n : ℕ) (hn : 4 ≤ n) (he : n % 2 = 0) :
    FactorialTailCriterion.scaledTail coeff n < n := by
  rw [scaledTail_eq n hn]
  have h : tail n < (n : ℤ) := by simp only [tail, he, if_true]; omega
  exact_mod_cast h

/-- Positive quadratic tails and the complete new descending congruence
family still admit a rational total. No claim about the target coefficients
or their sum is made by this theorem. -/
theorem comparison_properties :
    (∀ n : ℕ, 0 ≤ coeff n) ∧
    (∀ n : ℕ, 5 ≤ n → 0 < coeff n) ∧
    (∀ p : ℕ, 5 ≤ p → p.Prime → coeff p = 1) ∧
    (∀ n j : ℕ, 5 ≤ n → j < n.minFac →
      ((n - 1).descFactorial j : ℤ) ∣ coeff n - 1) ∧
    (∀ n : ℕ, 5 ≤ n → (n.minFac.factorial : ℤ) ∣ coeff n - 1) ∧
    (∀ n : ℕ, 4 ≤ n → 0 < FactorialTailCriterion.scaledTail coeff n ∧
      FactorialTailCriterion.scaledTail coeff n < (n : ℝ) ^ 2) ∧
    (∀ n : ℕ, 4 ≤ n → n % 2 = 0 →
      FactorialTailCriterion.scaledTail coeff n < n) ∧
    (∑' n : ℕ, (coeff n : ℝ) / n.factorial) = (1 / 24 : ℝ) := by
  exact ⟨coeff_nonneg, coeff_pos, coeff_prime, descending_congruence,
    minFac_factorial_congruence, strict_tail_bounds, even_tail_bound, sum_coeff⟩

#print axioms descending_congruence
#print axioms minFac_factorial_congruence
#print axioms comparison_properties

end DescendingCongruenceComparison
