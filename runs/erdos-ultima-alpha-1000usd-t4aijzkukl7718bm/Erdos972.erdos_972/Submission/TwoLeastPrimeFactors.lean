import Submission.MaskedPrimeSieve
import Submission.LeastFactorSmoothMangoldt

/-! The two least DISTINCT prime factors. Repeated powers are not counted
as a second factor. -/
namespace Erdos972TwoLeastPrimeFactors

open Finset ArithmeticFunction
open Erdos972MaskedPrimeSieve Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive
open Erdos972SharpSmoothMangoldt
set_option autoImplicit false

noncomputable def secondFac (n : ℕ) : ℕ :=
  if h : (n.primeFactors.erase n.minFac).Nonempty then
    (n.primeFactors.erase n.minFac).min' h else 1

noncomputable def twoLeastCost (n : ℕ) : ℝ := Real.log n.minFac * Real.log (secondFac n)

lemma erased_nonempty {n : ℕ} (hn0 : n ≠ 0) (hn1 : n ≠ 1)
    (hn : ¬ IsPrimePow n) : (n.primeFactors.erase n.minFac).Nonempty := by
  have hp := (Nat.minFac_prime hn1).mem_primeFactors (Nat.minFac_dvd n) hn0
  have hc : 0 < n.primeFactors.card := card_pos.mpr ⟨_, hp⟩
  have hc1 : n.primeFactors.card ≠ 1 :=
    fun h => hn (isPrimePow_iff_card_primeFactors_eq_one.mpr h)
  obtain ⟨q, hq, hqp⟩ := exists_mem_ne (show 1 < n.primeFactors.card by omega) n.minFac
  exact ⟨q, mem_erase.mpr ⟨hqp, hq⟩⟩

lemma secondFac_mem {n : ℕ} (hn : (n.primeFactors.erase n.minFac).Nonempty) :
    secondFac n ∈ n.primeFactors.erase n.minFac := by
  rw [secondFac, dif_pos hn]
  exact min'_mem _ _

lemma secondFac_le {n r : ℕ} (hn : (n.primeFactors.erase n.minFac).Nonempty)
    (hr : r ∈ n.primeFactors.erase n.minFac) : secondFac n ≤ r := by
  rw [secondFac, dif_pos hn]
  exact min'_le _ _ hr

lemma secondFac_eq_one_of_empty {n : ℕ}
    (hn : ¬ (n.primeFactors.erase n.minFac).Nonempty) : secondFac n = 1 := by
  exact dif_neg hn

lemma twoLeastCost_nonneg (n : ℕ) : 0 ≤ twoLeastCost n :=
  mul_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)

lemma twoLeastCost_zero_of_empty {n : ℕ}
    (hn : ¬ (n.primeFactors.erase n.minFac).Nonempty) : twoLeastCost n = 0 := by
  simp [twoLeastCost, secondFac_eq_one_of_empty hn]

lemma twoLeastCost_zero_of_primePower {n : ℕ} (hn : IsPrimePow n) :
    twoLeastCost n = 0 := by
  apply twoLeastCost_zero_of_empty
  intro he
  have hc := isPrimePow_iff_card_primeFactors_eq_one.mp hn
  have hp := (Nat.minFac_prime hn.ne_one).mem_primeFactors (Nat.minFac_dvd n) hn.ne_zero
  have hc' := card_erase_add_one hp
  have hcpos := card_pos.mpr he
  omega

lemma secondFac_noOtherSmallPrime {n R : ℕ} (hn0 : n ≠ 0)
    (hne : (n.primeFactors.erase n.minFac).Nonempty) (hR : R < secondFac n) :
    NoOtherSmallPrime R n.minFac n := by
  intro q hq hqR hqn
  by_contra hqp
  have hmem := mem_erase.mpr ⟨hqp, hq.mem_primeFactors hqn hn0⟩
  have hh := secondFac_le hne hmem
  omega

/-- For a non-prime-power, retain both least distinct factors rather than
replacing the second logarithm by log n. -/
theorem nonPrimePower_smooth_twoLeast {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : ¬ IsPrimePow n) : smoothMangoldt t n ≤ t*twoLeastCost n := by
  by_cases hn0 : n = 0
  · simp [hn0, smoothMangoldt, expDivisorSum, twoLeastCost, secondFac]
  by_cases hn1 : n = 1
  · simp [hn1, smoothMangoldt, expDivisorSum, twoLeastCost, secondFac]
  have he := erased_nonempty hn0 hn1 hn
  have hq := mem_erase.mp (secondFac_mem he)
  have hp := (Nat.minFac_prime hn1).mem_primeFactors (Nat.minFac_dvd n) hn0
  have hpbound : 1-Real.exp (-t*Real.log n.minFac) ≤ t*Real.log n.minFac := by
    linarith only [Real.add_one_le_exp (-t*Real.log n.minFac)]
  have hqbound : 1-Real.exp (-t*Real.log (secondFac n)) ≤ t*Real.log (secondFac n) := by
    linarith only [Real.add_one_le_exp (-t*Real.log (secondFac n))]
  have hb := (expDivisorSum_le_two_factors ht.le hn0 hp hq.2 hq.1.symm).trans
    (mul_le_mul hpbound hqbound (expFactor_nonneg ht.le _)
      (mul_nonneg ht.le (Real.log_natCast_nonneg _)))
  rw [smoothMangoldt, expDivisorSum_at_zero, one_apply, if_neg hn1, sub_zero]
  apply (div_le_iff₀ ht).mpr
  unfold twoLeastCost
  nlinarith only [hb]

lemma secondFac_le_self {n : ℕ} (hn : 0 < n) : secondFac n ≤ n := by
  by_cases he : (n.primeFactors.erase n.minFac).Nonempty
  · exact Nat.le_of_dvd hn (Nat.dvd_of_mem_primeFactors (mem_of_mem_erase (secondFac_mem he)))
  · rw [secondFac_eq_one_of_empty he]
    exact hn

/-- Only the non-prime-powers cost an error in this lower comparison.
On a prime power the smoothed value is already at most Mangoldt. -/
theorem smooth_le_mangoldt_add_twoLeast {t : ℝ} (ht : 0 < t) (n : ℕ) :
    smoothMangoldt t n ≤ Λ n+t*twoLeastCost n := by
  by_cases hn : IsPrimePow n
  · rw [twoLeastCost_zero_of_primePower hn, mul_zero, add_zero]
    have hn1 := hn.ne_one
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    rw [smoothMangoldt, expDivisorSum_at_zero, one_apply, if_neg hn1, sub_zero,
      expDivisorSum_prime_pow t hp hk, vonMangoldt_apply_pow hk.ne', vonMangoldt_apply_prime hp]
    apply (div_le_iff₀ ht).mpr
    linarith only [Real.add_one_le_exp (-t*Real.log p)]
  · rw [vonMangoldt_eq_zero_iff.mpr hn, zero_add]
    exact nonPrimePower_smooth_twoLeast ht hn

#print axioms nonPrimePower_smooth_twoLeast
#print axioms smooth_le_mangoldt_add_twoLeast
end Erdos972TwoLeastPrimeFactors
