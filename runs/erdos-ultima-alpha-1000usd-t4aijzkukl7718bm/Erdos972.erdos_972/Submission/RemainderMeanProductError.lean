import Submission.SparseSingleDivisorMoment
import Submission.MeanProductErrorAlgebra
import Submission.CenteredDoubleVaughan

/-! Quantitative control of the mean-product correction when replacing
Vaughan remainders by their prime-restricted versions. -/
namespace Erdos972RemainderMeanProductError
open Finset Classical
open Erdos972SparseSingleDivisorMoment Erdos972MeanProductErrorAlgebra
open Erdos972DoubleVaughan Erdos972PrimeFactorRemainder Erdos972PrimePowerError
open Erdos972LogarithmicCovariance Erdos972MellinRemainderEnergy
set_option maxHeartbeats 1200000
set_option autoImplicit false

lemma input_total_square {N : ℕ} {L : ℝ} (hL : 1+Real.log N ≤ L)
    (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ (n.divisors.card : ℝ)*Real.log n) :
    (total N f)^2 ≤ (N : ℝ)^2*L^5 :=
  divisor_log_sum_square (Ioc 0 N) (fun _ h => h) hL f (fun n _ => hf n)

lemma output_total_square {α L : ℝ} (hα : 1 ≤ α) {N : ℕ}
    (hL : 1+Real.log (floorMul α N) ≤ L)
    (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ (n.divisors.card : ℝ)*Real.log n) :
    (total N (fun n => f (floorMul α n)))^2 ≤ (floorMul α N : ℝ)^2*L^5 := by
  unfold total
  rw [sum_floor_eq_image hα]
  exact divisor_log_sum_square _ (floor_image_subset hα N) hL f (fun n _ => hf n)

lemma input_difference_total_square {U V Z N : ℕ} {L : ℝ}
    (hZ : 0 < Z) (hV : Z^3 ≤ V) (hL : 1+Real.log N ≤ L) :
    (total N (typeIIPart U V)-total N (primeTypeIIPart U V))^2 ≤
      4*(N : ℝ)^2*L^5/(Z : ℝ) := by
  simp only [total, ← sum_sub_distrib]
  exact remainder_difference_sum_square hZ hV (Ioc 0 N) (fun _ h => h) hL

lemma output_difference_total_square {α L : ℝ} (hα : 1 ≤ α) {U V Z N : ℕ}
    (hZ : 0 < Z) (hV : Z^3 ≤ V) (hL : 1+Real.log (floorMul α N) ≤ L) :
    (total N (fun n => typeIIPart U V (floorMul α n))-
      total N (fun n => primeTypeIIPart U V (floorMul α n)))^2 ≤
      4*(floorMul α N : ℝ)^2*L^5/(Z : ℝ) := by
  simp only [total, ← sum_sub_distrib]
  rw [sum_floor_eq_image hα N (fun n => typeIIPart U V n-primeTypeIIPart U V n)]
  exact remainder_difference_sum_square hZ hV _ (floor_image_subset hα N) hL

/-- The difference of the products of the two actual normalized means. -/
noncomputable def meanProductError (α : ℝ) (N U V : ℕ) : ℝ :=
  (total N (typeIIPart U V)*total N (fun n => typeIIPart U V (floorMul α n))-
    total N (primeTypeIIPart U V)*total N (fun n => primeTypeIIPart U V (floorMul α n)))/(N : ℝ)^2

lemma meanProductError_square_bound {α L : ℝ} (hα : 1 ≤ α) {N U V Z : ℕ}
    (hN : 0 < N) (hZ : 0 < Z) (hV : Z^3 ≤ V)
    (hiL : 1+Real.log N ≤ L) (hoL : 1+Real.log (floorMul α N) ≤ L) :
    (meanProductError α N U V)^2 ≤ 16*α^2*L^10/(Z : ℝ) := by
  have hL : 0 ≤ L := by linarith [Real.log_natCast_nonneg N]
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hZ0 : (0 : ℝ) < Z := Nat.cast_pos.mpr hZ
  have hα0 : 0 ≤ α := by linarith
  have hi := input_total_square hiL (primeTypeIIPart U V) (prime_remainder_abs_bound U V)
  have ho := output_total_square hα hoL (typeIIPart U V) (remainder_abs_bound U V)
  have he := input_difference_total_square (U := U) hZ hV hiL
  have hf := output_difference_total_square (U := U) hα hZ hV hoL
  have hh := product_difference_square_le (by positivity) (by positivity) (by positivity) (by positivity)
    hi ho he hf
  have hY := floorMul_le_real hα (le_refl N)
  have hb :
      (total N (typeIIPart U V)*total N (fun n => typeIIPart U V (floorMul α n))-
        total N (primeTypeIIPart U V)*total N (fun n => primeTypeIIPart U V (floorMul α n)))^2 ≤
        16*(N : ℝ)^2*(α*N)^2*L^10/(Z : ℝ) := by
    apply hh.trans
    calc
      _ = 16*(N : ℝ)^2*(floorMul α N : ℝ)^2*L^10/(Z : ℝ) := by ring
      _ ≤ _ := by gcongr
  unfold meanProductError
  rw [div_pow]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((N : ℝ)^2)^2)).mpr
  exact hb.trans_eq (by ring)

lemma meanProductError_fourth_bound {α L : ℝ} (hα : 1 ≤ α) {N U V Z : ℕ}
    (hN : 0 < N) (hZ : 0 < Z) (hV : Z^3 ≤ V)
    (hiL : 1+Real.log N ≤ L) (hoL : 1+Real.log (floorMul α N) ≤ L) :
    |meanProductError α N U V|^4 ≤ 256*α^4*L^20/(Z : ℝ)^2 := by
  have hh := pow_le_pow_left₀ (sq_nonneg _)
    (meanProductError_square_bound (U := U) hα hN hZ hV hiL hoL) 2
  rw [← pow_mul] at hh
  norm_num only [Nat.reduceMul] at hh
  rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ (meanProductError α N U V)^4)]
  exact hh.trans_eq (by ring)

#print axioms input_difference_total_square
#print axioms output_difference_total_square
#print axioms meanProductError_square_bound
#print axioms meanProductError_fourth_bound
end Erdos972RemainderMeanProductError
