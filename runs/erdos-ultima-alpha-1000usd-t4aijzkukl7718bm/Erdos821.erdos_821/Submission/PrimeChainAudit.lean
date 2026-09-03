import Submission.ReciprocalDensity

/-!
# A pointwise obstruction to a proposed prime-chain iteration

This does not disprove Erdős 821. It shows that applying the same weak
smoothness condition to every prime factor of a predecessor does not
square the smoothness exponent of the original predecessor.
-/

namespace Erdos821

private lemma primeFactors_ten : (10 : ℕ).primeFactors = {2, 5} := by
  have h := Nat.primeFactors_mul (a := 2) (b := 5) (by decide) (by decide)
  norm_num only [Nat.prime_two.primeFactors,
    (by norm_num : Nat.Prime 5).primeFactors, Finset.singleton_union] at h
  exact h

private lemma primeFactors_four : (4 : ℕ).primeFactors = {2} := by
  simpa only [Nat.prime_two.primeFactors] using
    Nat.primeFactors_pow (k := 2) 2 (by decide)

lemma eleven_mem_rational_smooth :
    11 ∈ rationalSmoothShiftedPrimes 4 3 := by
  change Nat.Prime 11 ∧ ∀ q ∈ (10 : ℕ).primeFactors, q ^ 4 ≤ 10 ^ 3
  rw [primeFactors_ten]
  norm_num

lemma eleven_children_mem_rational_smooth :
    ∀ q ∈ (11 - 1 : ℕ).primeFactors, q ∈ rationalSmoothShiftedPrimes 4 3 := by
  change ∀ q ∈ (10 : ℕ).primeFactors, q ∈ rationalSmoothShiftedPrimes 4 3
  rw [primeFactors_ten]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  constructor
  · change Nat.Prime 2 ∧ ∀ q ∈ (1 : ℕ).primeFactors, q ^ 4 ≤ 1 ^ 3
    norm_num
  · change Nat.Prime 5 ∧ ∀ q ∈ (4 : ℕ).primeFactors, q ^ 4 ≤ 4 ^ 3
    rw [primeFactors_four]
    norm_num

lemma eleven_not_mem_squared_rational_smooth :
    11 ∉ rationalSmoothShiftedPrimes 16 9 := by
  intro h
  have hh := h.2 5 (by rw [show 11 - 1 = (10 : ℕ) from rfl, primeFactors_ten]; simp)
  norm_num at hh

/-- Weak smoothness is not pointwise transitive along predecessor-prime
chains. The quantified implication fails already at the prime 11. -/
theorem rational_smoothness_not_transitive :
    ¬ (∀ a b p : ℕ, 0 < b → b < a →
      p ∈ rationalSmoothShiftedPrimes a b →
      (∀ q ∈ (p - 1).primeFactors, q ∈ rationalSmoothShiftedPrimes a b) →
      p ∈ rationalSmoothShiftedPrimes (a * a) (b * b)) := by
  intro H
  exact eleven_not_mem_squared_rational_smooth
    (H 4 3 11 (by decide) (by decide)
      eleven_mem_rational_smooth eleven_children_mem_rational_smooth)

#print axioms rational_smoothness_not_transitive

end Erdos821
