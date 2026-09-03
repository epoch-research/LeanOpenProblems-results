import Submission.LargeSquareDivisors
import Submission.MellinRemainderEnergy

/-! The Vaughan remainder with its large Mangoldt factors restricted to
primes agrees with the original outside a sparse large-square-divisor set. -/
namespace Erdos972PrimeFactorRemainder

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Erdos972Vaughan Erdos972DoubleVaughan Erdos972PrimePowerError
open Erdos972LargeSquareDivisors Erdos972MellinRemainderEnergy
set_option maxHeartbeats 1000000

noncomputable def primeMangoldt : ArithmeticFunction ℝ :=
  ⟨fun n => if n.Prime then Λ n else 0, by simp⟩

lemma primeMangoldt_nonneg (n : ℕ) : 0 ≤ primeMangoldt n := by
  change 0 ≤ if n.Prime then Λ n else 0
  split_ifs <;> first | exact vonMangoldt_nonneg | rfl

lemma primeMangoldt_le (n : ℕ) : primeMangoldt n ≤ Λ n := by
  change (if n.Prime then Λ n else 0) ≤ Λ n
  split_ifs <;> first | rfl | exact vonMangoldt_nonneg

noncomputable def primeTypeIIPart (U V : ℕ) : ArithmeticFunction ℝ :=
  tail (μ : ArithmeticFunction ℝ) U*ζ*tail primeMangoldt V

lemma typeII_dominated_abs_bound (g : ArithmeticFunction ℝ)
    (hg : ∀ n, 0 ≤ g n) (hgΛ : ∀ n, g n ≤ Λ n) (U V n : ℕ) :
    |(tail (μ : ArithmeticFunction ℝ) U*ζ*tail g V) n| ≤
      (n.divisors.card : ℝ)*Real.log n := by
  have htail (d : ℕ) : 0 ≤ tail g V d ∧ tail g V d ≤ Λ d := by
    by_cases hd : d ≤ V
    · rw [tail_eq_zero_of_le g hd]
      exact ⟨le_rfl, vonMangoldt_nonneg⟩
    · rw [tail_eq_of_lt g (by omega)]
      exact ⟨hg d, hgΛ d⟩
  rw [mul_comm _ (tail g V), ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d e => tail g V d*(tail (μ : ArithmeticFunction ℝ) U*ζ) e)]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ n.divisors, (n.divisors.card : ℝ)*Λ d := by
      apply sum_le_sum
      intro d hd
      have hdn := Nat.mem_divisors.mp hd
      have hc : ((n/d).divisors.card : ℝ) ≤ n.divisors.card := Nat.cast_le.mpr
        (card_le_card (Nat.divisors_subset_of_dvd hdn.2 (Nat.div_dvd_of_dvd hdn.1)))
      have ha := (abs_typeII_coefficient_le_card_divisors U (n/d)).trans hc
      rw [abs_mul, abs_of_nonneg (htail d).1]
      exact (mul_le_mul (htail d).2 ha (abs_nonneg _) vonMangoldt_nonneg).trans_eq (by ring)
    _ = _ := by rw [← mul_sum, vonMangoldt_sum]

lemma prime_remainder_abs_bound (U V n : ℕ) :
    |primeTypeIIPart U V n| ≤ (n.divisors.card : ℝ)*Real.log n :=
  typeII_dominated_abs_bound primeMangoldt primeMangoldt_nonneg primeMangoldt_le U V n

lemma prime_remainder_eq_of_no_large_square {U V N n : ℕ} (hV : U^3 ≤ V)
    (hn : n ∈ Ioc 0 N) (hnot : n ∉ largeSquareSet U N) :
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

lemma pair_difference_eq_zero_outside {α : ℝ} (hα : 1 ≤ α) {U V N n : ℕ}
    (hV : U^3 ≤ V) (hn : n ∈ Ioc 0 N) (hnot : n ∉ pairLargeSquareSet α U N) :
    typeIIPart U V n*typeIIPart U V (floorMul α n) -
      primeTypeIIPart U V n*primeTypeIIPart U V (floorMul α n) = 0 := by
  have hn' : floorMul α n ∈ Ioc 0 (floorMul α N) := mem_Ioc.mpr
    ⟨floorMul_pos hα (mem_Ioc.mp hn).1, (floorMul_strictMono hα).monotone (mem_Ioc.mp hn).2⟩
  have hi : n ∉ largeSquareSet U N := by
    intro hh
    exact hnot (mem_filter.mpr ⟨hn, Or.inl hh⟩)
  have ho : floorMul α n ∉ largeSquareSet U (floorMul α N) := by
    intro hh
    exact hnot (mem_filter.mpr ⟨hn, Or.inr hh⟩)
  rw [prime_remainder_eq_of_no_large_square hV hn hi,
    prime_remainder_eq_of_no_large_square hV hn' ho, sub_self]

lemma pair_difference_abs_bound {α L : ℝ} (hα : 1 ≤ α) {U V N n : ℕ}
    (hn : n ∈ Ioc 0 N) (hL : 0 ≤ L) (hiL : Real.log N ≤ L)
    (hoL : Real.log (floorMul α N) ≤ L) :
    |typeIIPart U V n*typeIIPart U V (floorMul α n) -
      primeTypeIIPart U V n*primeTypeIIPart U V (floorMul α n)| ≤
      (2*L^2)*(n.divisors.card : ℝ)*(floorMul α n).divisors.card := by
  have hl₁ := (log_input_le hn).trans hiL
  have hl₂ : Real.log (floorMul α n) ≤ L := (Real.log_le_log
    (Nat.cast_pos.mpr (floorMul_pos hα (mem_Ioc.mp hn).1))
    (Nat.cast_le.mpr ((floorMul_strictMono hα).monotone (mem_Ioc.mp hn).2))).trans hoL
  have hb (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ (n.divisors.card : ℝ)*Real.log n) :
      |f n*f (floorMul α n)| ≤
        L^2*(n.divisors.card : ℝ)*(floorMul α n).divisors.card := by
    rw [abs_mul]
    have h1 := (hf n).trans (mul_le_mul_of_nonneg_left hl₁ (Nat.cast_nonneg _))
    have h2 := (hf (floorMul α n)).trans (mul_le_mul_of_nonneg_left hl₂ (Nat.cast_nonneg _))
    exact (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have h₁ := hb (typeIIPart U V) (remainder_abs_bound U V)
  have h₂ := hb (primeTypeIIPart U V) (prime_remainder_abs_bound U V)
  exact (abs_sub _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

#print axioms prime_remainder_eq_of_no_large_square
#print axioms pair_difference_abs_bound
end Erdos972PrimeFactorRemainder
