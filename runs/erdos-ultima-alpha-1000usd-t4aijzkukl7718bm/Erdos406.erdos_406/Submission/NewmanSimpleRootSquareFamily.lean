import Submission.NewmanReverseValuation
import Submission.SquareRootObstruction

/-! An infinite obstruction to replacing the exact power-of-two value by a
square value, even in the simple-root-at-one branch modulo two. Every member
retains the odd divisor five. This is NOT a disproof of Erdős 406. -/

namespace Erdos406SimpleRootSquares
open Polynomial Erdos406Work Erdos406Cyclotomic Erdos406SimpleModTwoRoot
  Erdos406ReverseValuation

lemma digits_sum_add_shifted {a b L : ℕ} (ha : a < 3 ^ L) :
    (Nat.digits 3 (a + 3 ^ L * b)).sum = (Nat.digits 3 a).sum + (Nat.digits 3 b).sum := by
  by_cases hb : b = 0
  · simp [hb]
  have hl : (Nat.digits 3 a).length ≤ L :=
    (Nat.digits_length_le_iff (by decide : 1 < 3) a).mpr ha
  have hh := Nat.digits_append_zeroes_append_digits (b := 3)
    (k := L - (Nat.digits 3 a).length) (m := b) (n := a) (by decide) (by omega)
  rw [show (Nat.digits 3 a).length + (L - (Nat.digits 3 a).length) = L by omega] at hh
  rw [← hh]
  simp

/-- The separated three-block square construction always has exactly
thirty-eight ternary ones. -/
theorem affine_square_digit_sum (j : ℕ) (hj : 9 ≤ j) :
    (Nat.digits 3 ((8035 + 11645 * 9 ^ j) ^ 2)).sum = 38 := by
  have hp : 3 ^ 18 ≤ 3 ^ (2 * j) := Nat.pow_le_pow_right (by decide) (by omega)
  have ha : 8035 ^ 2 < 3 ^ (2 * j) := lt_of_lt_of_le (by decide) hp
  have hab : 2 * 8035 * 11645 < 3 ^ (2 * j) := lt_of_lt_of_le (by decide) hp
  have he : (8035 + 11645 * 9 ^ j) ^ 2 =
      8035 ^ 2 + 3 ^ (2 * j) * (2 * 8035 * 11645 + 3 ^ (2 * j) * 11645 ^ 2) := by
    rw [show (9 : ℕ) = 3 ^ 2 by decide, pow_mul]
    ring
  rw [he, digits_sum_add_shifted ha, digits_sum_add_shifted hab]
  norm_num [Nat.digits_of_two_le_of_pos]

lemma affine_root_eight_dvd (j : ℕ) : 8 ∣ 8035 + 11645 * 9 ^ j := by
  apply Nat.dvd_of_mod_eq_zero
  simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]

lemma affine_square_sixteen_dvd (j : ℕ) :
    (16 : ℤ) ∣ (digitPoly (Nat.digits 3 ((8035 + 11645 * 9 ^ j) ^ 2))).eval 3 := by
  rw [digitPoly_eval_three]
  norm_cast
  obtain ⟨t, ht⟩ := affine_root_eight_dvd j
  refine ⟨4 * t ^ 2, ?_⟩
  rw [ht]
  ring

/-- This verifies the simple-root property for every member, not merely
for a few computed examples. -/
theorem affine_square_simple_one (j : ℕ) (hj : 9 ≤ j) :
    SimpleOne (digitPoly (Nat.digits 3 ((8035 + 11645 * 9 ^ j) ^ 2))) := by
  have h4 : (4 : ℤ) ∣ (digitPoly (Nat.digits 3 ((8035 + 11645 * 9 ^ j) ^ 2))).eval 3 :=
    dvd_trans (by norm_num : (4 : ℤ) ∣ 16) (affine_square_sixteen_dvd j)
  apply (simple_one_iff_eval_one_mod_four _ h4).mpr
  change (Nat.ofDigits (X : ℤ[X]) (Nat.digits 3 ((8035 + 11645 * 9 ^ j) ^ 2))).eval 1 % 4 = 2
  rw [Erdos406Newman.eval_one_digitPoly, affine_square_digit_sum j hj]
  norm_num

theorem affine_square_reverse_eight (j : ℕ) (hj : 9 ≤ j) :
    (digitPoly (Nat.digits 3 ((8035 + 11645 * 9 ^ j) ^ 2))).reverse.eval 3 % 16 = 8 :=
  simple_one_reverse_eval_eight _ (affine_square_sixteen_dvd j) (affine_square_simple_one j hj)

/-- Arbitrarily large roots and arbitrary fixed two-adic divisibility are
compatible with good square digits, a simple mod-two root, and the exact
reciprocal residue eight. The squares are not powers of two. -/
theorem arbitrarily_large_simple_root_squares (K B : ℕ) :
    ∃ n : ℕ, B < n ∧ 2 ^ K ∣ n ∧ 5 ∣ n ∧
      Nat.digits 3 (n ^ 2) ⊆ [0, 1] ∧
      SimpleOne (digitPoly (Nat.digits 3 (n ^ 2))) ∧
      (digitPoly (Nat.digits 3 (n ^ 2))).reverse.eval 3 % 16 = 8 ∧
      ¬ (n ^ 2).isPowerOfTwo := by
  obtain ⟨j, hj, hd⟩ := affine_nine_pow_divisible 8035 11645 (B + 9) K
    (by decide) (by decide)
  let n := 8035 + 11645 * 9 ^ j
  have hn5 : 5 ∣ n := by
    dsimp [n]
    exact dvd_add (by decide) (dvd_mul_of_dvd_left (by decide) _)
  have hnlarge : B < n := by
    have hp : j < 9 ^ j := Nat.lt_pow_self (by decide)
    dsimp [n]
    omega
  refine ⟨n, hnlarge, (pow_dvd_pow 2 (by omega : K ≤ K + 3)).trans hd, hn5,
    good_square_affine_nine j (by omega), affine_square_simple_one j (by omega),
    affine_square_reverse_eight j (by omega), ?_⟩
  rintro ⟨k, hk⟩
  have hh : 5 ∣ n ^ 2 := hn5.trans (dvd_pow_self n (by decide : 2 ≠ 0))
  rw [hk] at hh
  have h2 := Nat.prime_five.dvd_of_dvd_pow hh
  norm_num at h2

/-- Coprime odd blocks can also occur in separated good-square constructions.
This pair does not have the high-divisibility property of the main family:
`29 + 55 * 9^j` is always four modulo eight. -/
lemma coprime_odd_square_blocks :
    Nat.Coprime 29 55 ∧ Odd (29 : ℕ) ∧ Odd (55 : ℕ) ∧
      Nat.digits 3 (29 ^ 2) ⊆ [0, 1] ∧
      Nat.digits 3 (2 * 29 * 55) ⊆ [0, 1] ∧
      Nat.digits 3 (55 ^ 2) ⊆ [0, 1] := by
  decide +kernel

lemma coprime_block_root_residue (j : ℕ) : (29 + 55 * 9 ^ j) % 8 = 4 := by
  simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]

#print axioms affine_square_digit_sum
#print axioms affine_square_simple_one
#print axioms coprime_odd_square_blocks
#print axioms arbitrarily_large_simple_root_squares
end Erdos406SimpleRootSquares
