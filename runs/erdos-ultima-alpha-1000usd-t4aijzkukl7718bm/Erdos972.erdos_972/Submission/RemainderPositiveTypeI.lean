import Submission.RemainderRoughSupport

/-! The positive part of the actual Vaughan remainder is a function of its
Type-I part alone. This is a structural identity, not a covariance estimate. -/
namespace Erdos972RemainderPositiveTypeI

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Erdos972Vaughan Erdos972DoubleVaughan Erdos972TypeIPolynomial

lemma moebius_nonpos_of_isPrimePow {n : ℕ} (hn : IsPrimePow n) : (μ n : ℝ) ≤ 0 := by
  by_cases hp : n.Prime
  · rw [moebius_apply_prime hp]
    norm_num
  · rw [moebius_apply_isPrimePow_not_prime hn hp]
    norm_num

lemma tail_moebius_nonpos_on_divisor {U n d : ℕ} (hU : 1 ≤ U)
    (hn : IsPrimePow n) (hd : d ∣ n) : tail (μ : ArithmeticFunction ℝ) U d ≤ 0 := by
  by_cases hdU : d ≤ U
  · rw [tail_eq_zero_of_le _ hdU]
  · have hd1 : d ≠ 1 := by omega
    rw [tail_eq_of_lt _ (lt_of_not_ge hdU), intCoe_apply]
    exact moebius_nonpos_of_isPrimePow (hn.dvd hd hd1)

lemma tail_moebius_zeta_nonpos_on_divisor {U n d : ℕ} (hU : 1 ≤ U)
    (hn : IsPrimePow n) (hd : d ∣ n) : (tail (μ : ArithmeticFunction ℝ) U * ζ) d ≤ 0 := by
  rw [coe_mul_zeta_apply]
  apply sum_nonpos
  intro e he
  exact tail_moebius_nonpos_on_divisor hU hn ((Nat.dvd_of_mem_divisors he).trans hd)

/-- The remainder is nonpositive on every prime power, for all Mangoldt
cutoffs, including a zero Mangoldt cutoff. The positive Mobius cutoff matters. -/
theorem typeIIPart_isPrimePow_nonpos {U V n : ℕ} (hU : 1 ≤ U)
    (hn : IsPrimePow n) : typeIIPart U V n ≤ 0 := by
  rw [typeIIPart, ArithmeticFunction.mul_apply]
  apply sum_nonpos
  intro ab hab
  have he := (Nat.mem_divisorsAntidiagonal.mp hab).1
  have ha : ab.1 ∣ n := he ▸ dvd_mul_right ab.1 ab.2
  exact mul_nonpos_of_nonpos_of_nonneg
    (tail_moebius_zeta_nonpos_on_divisor hU hn ha) (tail_vonMangoldt_nonneg V ab.2)

lemma typeIPart_ge_mangoldt_on_prime_power {U V n : ℕ} (hU : 1 ≤ U)
    (hn : IsPrimePow n) : Λ n ≤ typeIPart U V n := by
  have he := congrArg (fun f : ArithmeticFunction ℝ => f n) (mangoldt_split U V)
  simp only [ArithmeticFunction.add_apply] at he
  linarith only [he, typeIIPart_isPrimePow_nonpos (V := V) hU hn]

/-- Unlike the unmodified Type-I expression, its positive part really is a
pointwise majorant of the von Mangoldt function. -/
theorem mangoldt_le_positive_typeI {U : ℕ} (hU : 1 ≤ U) (V n : ℕ) :
    Λ n ≤ max (typeIPart U V n) 0 := by
  by_cases hn : IsPrimePow n
  · exact (typeIPart_ge_mangoldt_on_prime_power hU hn).trans (le_max_left _ _)
  · rw [vonMangoldt_eq_zero_iff.mpr hn]
    exact le_max_right _ _

/-- This exact identity removes the Mangoldt function from the positive
remainder. It does not make that positive part negligible. -/
theorem positive_remainder_eq_negative_typeI {U : ℕ} (hU : 1 ≤ U) (V n : ℕ) :
    max (typeIIPart U V n) 0 = max (-typeIPart U V n) 0 := by
  by_cases hn : IsPrimePow n
  · have hr := typeIIPart_isPrimePow_nonpos (V := V) hU hn
    have ha : 0 ≤ typeIPart U V n :=
      vonMangoldt_nonneg.trans (typeIPart_ge_mangoldt_on_prime_power hU hn)
    rw [max_eq_right hr, max_eq_right (neg_nonpos.mpr ha)]
  · have he := congrArg (fun f : ArithmeticFunction ℝ => f n) (mangoldt_split U V)
    simp only [ArithmeticFunction.add_apply, vonMangoldt_eq_zero_iff.mpr hn] at he
    congr 1
    linarith only [he]

/-- The negative remainder is exactly the residual of the genuine positive
Type-I majorant. -/
theorem negative_remainder_eq_majorant_residual {U : ℕ} (hU : 1 ≤ U) (V n : ℕ) :
    max (-typeIIPart U V n) 0 = max (typeIPart U V n) 0 - Λ n := by
  have he := congrArg (fun f : ArithmeticFunction ℝ => f n) (mangoldt_split U V)
  simp only [ArithmeticFunction.add_apply] at he
  have hp := positive_remainder_eq_negative_typeI hU V n
  rcases le_total (typeIIPart U V n) 0 with hr | hr
  · rw [max_eq_right hr] at hp
    have ha : 0 ≤ typeIPart U V n := by
      have := le_max_left (-typeIPart U V n) 0
      linarith only [hp, this]
    rw [max_eq_left (neg_nonneg.mpr hr), max_eq_left ha]
    linarith only [he]
  · rw [max_eq_left hr] at hp
    rcases le_total (typeIPart U V n) 0 with ha | ha
    · rw [max_eq_left (neg_nonneg.mpr ha)] at hp
      rw [max_eq_right (neg_nonpos.mpr hr), max_eq_right ha]
      linarith only [he, hp]
    · rw [max_eq_right (neg_nonpos.mpr ha)] at hp
      rw [max_eq_right (neg_nonpos.mpr hr), max_eq_left ha]
      linarith only [he, hp]

#print axioms typeIIPart_isPrimePow_nonpos
#print axioms mangoldt_le_positive_typeI
#print axioms positive_remainder_eq_negative_typeI
#print axioms negative_remainder_eq_majorant_residual

end Erdos972RemainderPositiveTypeI
