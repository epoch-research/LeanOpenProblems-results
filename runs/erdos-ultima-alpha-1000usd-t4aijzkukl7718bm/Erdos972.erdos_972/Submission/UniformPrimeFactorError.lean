import Submission.PrimeFactorError

/-! Proper-prime-power removal with a square-divisor threshold independent
of the Mobius cutoff. No signed correlation estimate is asserted. -/
namespace Erdos972UniformPrimeFactorError
open Finset
open Erdos972PrimePowerError Erdos972DoubleVaughan Erdos972Vaughan
open Erdos972LargeSquareDivisors Erdos972PrimeFactorRemainder
open Erdos972PrimeFactorError Erdos972SparseDivisorMoment
open ArithmeticFunction
set_option maxHeartbeats 1000000

lemma prime_remainder_eq_of_no_large_square_general {U V Z N n : ℕ} (hV : Z^3 ≤ V)
    (hn : n ∈ Ioc 0 N) (hnot : n ∉ largeSquareSet Z N) :
    primeTypeIIPart U V n = typeIIPart U V n := by
  unfold primeTypeIIPart typeIIPart
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  apply sum_congr rfl
  intro ab hab
  congr 1
  by_cases hdV : ab.2 ≤ V
  · rw [tail_eq_zero_of_le primeMangoldt hdV, tail_eq_zero_of_le Λ hdV]
  · have hdV' : V < ab.2 := by omega
    rw [tail_eq_of_lt primeMangoldt hdV', tail_eq_of_lt Λ hdV']
    change (if ab.2.Prime then Λ ab.2 else 0) = Λ ab.2
    split_ifs with hp
    · rfl
    · by_contra hh
      have hΛ : Λ ab.2 ≠ 0 := Ne.symm hh
      have hpow := vonMangoldt_ne_zero_iff.mp hΛ
      have hd : ab.2 ∣ n := by
        rw [← (Nat.mem_divisorsAntidiagonal.mp hab).1]
        exact dvd_mul_left _ _
      exact hnot (prime_power_divisor_mem hn hd hpow hp (hV.trans_lt hdV'))

lemma pair_difference_eq_zero_outside_general {α : ℝ} (hα : 1 ≤ α) {U V Z N n : ℕ}
    (hV : Z^3 ≤ V) (hn : n ∈ Ioc 0 N) (hnot : n ∉ pairLargeSquareSet α Z N) :
    typeIIPart U V n*typeIIPart U V (floorMul α n) -
      primeTypeIIPart U V n*primeTypeIIPart U V (floorMul α n) = 0 := by
  have hn' : floorMul α n ∈ Ioc 0 (floorMul α N) := mem_Ioc.mpr
    ⟨floorMul_pos hα (mem_Ioc.mp hn).1, (floorMul_strictMono hα).monotone (mem_Ioc.mp hn).2⟩
  have hi : n ∉ largeSquareSet Z N := by
    intro hh
    exact hnot (mem_filter.mpr ⟨hn, Or.inl hh⟩)
  have ho : floorMul α n ∉ largeSquareSet Z (floorMul α N) := by
    intro hh
    exact hnot (mem_filter.mpr ⟨hn, Or.inr hh⟩)
  rw [prime_remainder_eq_of_no_large_square_general hV hn hi,
    prime_remainder_eq_of_no_large_square_general hV hn' ho, sub_self]

lemma primeFactorError_eq_sparse_sum_general {α : ℝ} (hα : 1 ≤ α) {N U V Z : ℕ}
    (hV : Z^3 ≤ V) :
    primeFactorError α N U V =
      ∑ n ∈ pairLargeSquareSet α Z N,
        (typeIIPart U V n*typeIIPart U V (floorMul α n) -
          primeTypeIIPart U V n*primeTypeIIPart U V (floorMul α n)) := by
  unfold primeFactorError pairSum
  rw [← sum_sub_distrib]
  symm
  apply sum_subset (pairLargeSquareSet_subset α Z N)
  intro n hn hnot
  exact pair_difference_eq_zero_outside_general hα hV hn hnot

lemma primeFactorError_fourth_bound_general {α L : ℝ} (hα : 1 ≤ α) {N U V Z : ℕ}
    (hZ : 0 < Z) (hV : Z^3 ≤ V)
    (hiL : 1+Real.log N ≤ L) (hoL : 1+Real.log (floorMul α N) ≤ L) :
    |primeFactorError α N U V|^4 ≤
      16*((N : ℝ)+floorMul α N)^2/(Z : ℝ)^2 *
        (N : ℝ)*(floorMul α N : ℝ)*L^38 := by
  have hL : 0 ≤ L := by linarith [Real.log_natCast_nonneg N]
  have hh := sparse_sum_fourth_bound hα (pairLargeSquareSet α Z N)
    (pairLargeSquareSet_subset α Z N) hiL hoL
    (fun n => typeIIPart U V n*typeIIPart U V (floorMul α n) -
      primeTypeIIPart U V n*primeTypeIIPart U V (floorMul α n)) (fun n hn =>
      pair_difference_abs_bound hα (pairLargeSquareSet_subset α Z N hn) hL
        (by linarith only [hiL]) (by linarith only [hoL]))
  rw [← primeFactorError_eq_sparse_sum_general hα hV] at hh
  apply hh.trans
  have hcard := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) _)
    (pairLargeSquareSet_card_le hα hZ N) 2
  calc
    _ ≤ (2*L^2)^4 * (((N : ℝ)+floorMul α N)/Z)^2 *
        (N : ℝ)*(floorMul α N : ℝ)*L^30 := by gcongr
    _ = _ := by ring

lemma primeFactorError_normalized_fourth_general {α L : ℝ} (hα : 1 ≤ α) {N U V Z : ℕ}
    (hN : 0 < N) (hZ : 0 < Z) (hV : Z^3 ≤ V)
    (hiL : 1+Real.log N ≤ L) (hoL : 1+Real.log (floorMul α N) ≤ L) :
    |primeFactorError α N U V/(N : ℝ)|^4 ≤
      16*α*(1+α)^2*L^38/(Z : ℝ)^2 := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hZ0 : (0 : ℝ) < Z := Nat.cast_pos.mpr hZ
  have hα0 : 0 ≤ α := by linarith
  have hL : 0 ≤ L := by linarith [Real.log_natCast_nonneg N]
  have hY : (floorMul α N : ℝ) ≤ α*N := floorMul_le_real hα le_rfl
  have hNY : (N : ℝ)+floorMul α N ≤ (1+α)*N := by nlinarith only [hY]
  have hh := primeFactorError_fourth_bound_general (U := U) hα hZ hV hiL hoL
  have hb : |primeFactorError α N U V|^4 ≤
      16*((1+α)*(N : ℝ))^2/(Z : ℝ)^2*(N : ℝ)*(α*N)*L^38 := by
    apply hh.trans
    gcongr
  rw [abs_div, abs_of_pos hN0, div_pow]
  apply (div_le_iff₀ (pow_pos hN0 4)).mpr
  exact hb.trans_eq (by ring)

#print axioms primeFactorError_normalized_fourth_general
end Erdos972UniformPrimeFactorError
