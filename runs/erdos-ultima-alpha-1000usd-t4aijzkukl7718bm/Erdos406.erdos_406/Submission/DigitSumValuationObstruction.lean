import Submission.Work

/-! An exact obstruction to two proposed whole-polynomial valuation bounds.
The example has odd part 4745, so it does not disprove Erdős 406. No uniform
subcritical linear valuation bound is established or refuted here. -/
namespace Erdos406DigitSumValuation

def exampleN : ℕ := 667799382246031360

lemma example_digits : Nat.digits 3 exampleN ⊆ [0, 1] ∧
    (Nat.digits 3 exampleN).length = 38 ∧
    (Nat.digits 3 exampleN).sum = 22 := by
  decide +kernel

lemma example_factorization : exampleN = 2 ^ 47 * 4745 := by
  norm_num [exampleN]

lemma example_valuation : padicValNat 2 exampleN = 47 := by
  rw [example_factorization, padicValNat.mul (by positivity) (by decide),
    padicValNat.prime_pow]
  have h : padicValNat 2 4745 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
  rw [h, add_zero]

lemma example_not_power_of_two : ¬ exampleN.isPowerOfTwo := by
  rintro ⟨k, hk⟩
  have h5 : 5 ∣ exampleN := by decide +kernel
  rw [hk] at h5
  have hh := (by decide : Nat.Prime 5).dvd_of_dvd_pow h5
  norm_num at hh

/-- The degree-plus-twice-valuation-of-digit-sum estimate fails even for a
normalized binary-coefficient polynomial. -/
theorem degree_and_digit_sum_valuation_bound_false :
    ¬ (∀ n : ℕ, 0 < n → Nat.digits 3 n ⊆ [0, 1] →
      padicValNat 2 n ≤ (Nat.digits 3 n).length - 1 +
        2 * padicValNat 2 (Nat.digits 3 n).sum) := by
  intro h
  have hh := h exampleN (by decide) example_digits.1
  rw [example_valuation, example_digits.2.1, example_digits.2.2] at hh
  have h22 : padicValNat 2 22 = 1 := by
    rw [show 22 = 2 ^ 1 * 11 by norm_num,
      padicValNat.mul (by decide) (by decide), padicValNat.prime_pow]
    have hi : padicValNat 2 11 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
    rw [hi, add_zero]
  rw [h22] at hh
  norm_num at hh

/-- Even replacing the valuation of the digit sum by its real logarithmic
size does not rescue the estimate with zero additive allowance. This uses
an integer formulation, so no logarithms or numerical estimates are involved. -/
theorem degree_and_digit_sum_size_bound_false :
    ¬ (∀ n : ℕ, 0 < n → Nat.digits 3 n ⊆ [0, 1] →
      2 ^ padicValNat 2 n ≤ 2 ^ ((Nat.digits 3 n).length - 1) *
        (Nat.digits 3 n).sum ^ 2) := by
  intro h
  have hh := h exampleN (by decide) example_digits.1
  rw [example_valuation, example_digits.2.1, example_digits.2.2] at hh
  norm_num at hh

/-- This example does NOT violate the earlier, still-unproved slope-three-
over-two valuation gap. It must not be used to claim that gap is false. -/
lemma example_satisfies_three_halves_gap :
    2 * padicValNat 2 exampleN ≤ 3 * (Nat.digits 3 exampleN).length := by
  rw [example_valuation, example_digits.2.1]
  norm_num

#print axioms degree_and_digit_sum_valuation_bound_false
#print axioms degree_and_digit_sum_size_bound_false
#print axioms example_not_power_of_two
end Erdos406DigitSumValuation
