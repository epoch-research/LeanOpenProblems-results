import Submission.PrimeFactorRemainder
import Submission.SparseDivisorMoment

/-! An absolute error bound for replacing both large Mangoldt factors in
the double Vaughan remainder by primes. This does not estimate the remaining
signed correlation of the prime-restricted remainders. -/
namespace Erdos972PrimeFactorError

open Finset
open Erdos972PrimePowerError Erdos972DoubleVaughan
open Erdos972LargeSquareDivisors Erdos972PrimeFactorRemainder
open Erdos972SparseDivisorMoment
set_option maxHeartbeats 1000000

noncomputable def primeFactorError (α : ℝ) (N U V : ℕ) : ℝ :=
  pairSum α N (typeIIPart U V) (typeIIPart U V) -
    pairSum α N (primeTypeIIPart U V) (primeTypeIIPart U V)

lemma primeFactorError_eq_sparse_sum {α : ℝ} (hα : 1 ≤ α) {N U V : ℕ}
    (hV : U^3 ≤ V) :
    primeFactorError α N U V =
      ∑ n ∈ pairLargeSquareSet α U N,
        (typeIIPart U V n*typeIIPart U V (floorMul α n) -
          primeTypeIIPart U V n*primeTypeIIPart U V (floorMul α n)) := by
  unfold primeFactorError pairSum
  rw [← sum_sub_distrib]
  symm
  apply sum_subset (pairLargeSquareSet_subset α U N)
  intro n hn hnot
  exact pair_difference_eq_zero_outside hα hV hn hnot

lemma primeFactorError_fourth_bound {α L : ℝ} (hα : 1 ≤ α) {N U V : ℕ}
    (hU : 0 < U) (hV : U^3 ≤ V)
    (hiL : 1+Real.log N ≤ L) (hoL : 1+Real.log (floorMul α N) ≤ L) :
    |primeFactorError α N U V|^4 ≤
      16*((N : ℝ)+floorMul α N)^2/(U : ℝ)^2 *
        (N : ℝ)*(floorMul α N : ℝ)*L^38 := by
  have hL : 0 ≤ L := by linarith [Real.log_natCast_nonneg N]
  have hh := sparse_sum_fourth_bound hα (pairLargeSquareSet α U N)
    (pairLargeSquareSet_subset α U N) hiL hoL
    (fun n => typeIIPart U V n*typeIIPart U V (floorMul α n) -
      primeTypeIIPart U V n*primeTypeIIPart U V (floorMul α n)) (fun n hn =>
      pair_difference_abs_bound hα (pairLargeSquareSet_subset α U N hn) hL
        (by linarith only [hiL]) (by linarith only [hoL]))
  rw [← primeFactorError_eq_sparse_sum hα hV] at hh
  apply hh.trans
  have hcard := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) _)
    (pairLargeSquareSet_card_le hα hU N) 2
  calc
    _ ≤ (2*L^2)^4 * (((N : ℝ)+floorMul α N)/U)^2 *
        (N : ℝ)*(floorMul α N : ℝ)*L^30 := by gcongr
    _ = _ := by ring

lemma primeFactorError_normalized_fourth {α L : ℝ} (hα : 1 ≤ α) {N U V : ℕ}
    (hN : 0 < N) (hU : 0 < U) (hV : U^3 ≤ V)
    (hiL : 1+Real.log N ≤ L) (hoL : 1+Real.log (floorMul α N) ≤ L) :
    |primeFactorError α N U V/(N : ℝ)|^4 ≤
      16*α*(1+α)^2*L^38/(U : ℝ)^2 := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hU0 : (0 : ℝ) < U := Nat.cast_pos.mpr hU
  have hα0 : 0 ≤ α := by linarith
  have hL : 0 ≤ L := by linarith [Real.log_natCast_nonneg N]
  have hY : (floorMul α N : ℝ) ≤ α*N := floorMul_le_real hα le_rfl
  have hNY : (N : ℝ)+floorMul α N ≤ (1+α)*N := by nlinarith only [hY]
  have hh := primeFactorError_fourth_bound hα hU hV hiL hoL
  have hb : |primeFactorError α N U V|^4 ≤
      16*((1+α)*(N : ℝ))^2/(U : ℝ)^2*(N : ℝ)*(α*N)*L^38 := by
    apply hh.trans
    gcongr
  rw [abs_div, abs_of_pos hN0, div_pow]
  apply (div_le_iff₀ (pow_pos hN0 4)).mpr
  exact hb.trans_eq (by ring)

#print axioms primeFactorError_eq_sparse_sum
#print axioms primeFactorError_normalized_fourth
end Erdos972PrimeFactorError
