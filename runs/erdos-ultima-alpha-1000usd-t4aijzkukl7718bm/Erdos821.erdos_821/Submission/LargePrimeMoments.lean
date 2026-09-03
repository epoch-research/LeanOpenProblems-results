import Submission.StructuredSecondSieve

/-!
# Exact large-prime-factor moments of shifted primes

Bonferroni inequalities make explicit the information omitted by a first-moment
rough-prime sieve. These are finite identities; no analytic estimates for the
new higher moments are asserted here.
-/

open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators

namespace Erdos821

open AnalyticSieve

set_option maxHeartbeats 2000000

noncomputable def largePrimeDivisors (Y n : ℕ) : Finset ℕ :=
  n.primeFactors.filter (fun q => Y ≤ q)

lemma largePrimeDivisors_card_zero_iff (Y n : ℕ) (hn : 0 < n) :
    (largePrimeDivisors Y n).card = 0 ↔ n ∈ Nat.smoothNumbers Y := by
  rw [Finset.card_eq_zero, eq_empty_iff_forall_notMem]
  constructor
  · intro h
    apply Nat.mem_smoothNumbers'.mpr
    intro q hq hqd
    by_contra hqY
    exact h q (mem_filter.mpr ⟨hq.mem_primeFactors hqd hn.ne', by omega⟩)
  · intro h q hq
    obtain ⟨hqN, hYq⟩ := mem_filter.mp hq
    have hlt := Nat.mem_smoothNumbers'.mp h q (Nat.prime_of_mem_primeFactors hqN)
      (Nat.dvd_of_mem_primeFactors hqN)
    omega

lemma smooth_divisor_large_prime_product_dvd (Y n d : ℕ)
    (hdY : d ∈ Nat.smoothNumbers Y) (hdn : d ∣ n) :
    d * (∏ q ∈ largePrimeDivisors Y n, q) ∣ n := by
  have hprime (q : ℕ) (hq : q ∈ largePrimeDivisors Y n) : q.Prime :=
    Nat.prime_of_mem_primeFactors (mem_filter.mp hq).1
  have hprod : (∏ q ∈ largePrimeDivisors Y n, q) ∣ n :=
    (Sieve.prod_primes_dvd_iff _ hprime n).mpr
      (fun q hq => Nat.dvd_of_mem_primeFactors (mem_filter.mp hq).1)
  have hcop : d.Coprime (∏ q ∈ largePrimeDivisors Y n, q) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    apply ((hprime q hq).coprime_iff_not_dvd.mpr ?_).symm
    intro hqd
    have hlt := Nat.mem_smoothNumbers'.mp hdY q (hprime q hq) hqd
    have hle := (mem_filter.mp hq).2
    omega
  exact hcop.mul_dvd_of_dvd_of_dvd hdn hprod

lemma smooth_divisor_large_prime_power_le (Y n d : ℕ) (hn : 0 < n)
    (hdY : d ∈ Nat.smoothNumbers Y) (hdn : d ∣ n) :
    d * Y ^ (largePrimeDivisors Y n).card ≤ n := by
  have hprod : Y ^ (largePrimeDivisors Y n).card ≤ ∏ q ∈ largePrimeDivisors Y n, q := by
    calc
      _ = ∏ _q ∈ largePrimeDivisors Y n, Y := by simp
      _ ≤ _ := prod_le_prod' (fun _ hq => (mem_filter.mp hq).2)
  exact (Nat.mul_le_mul_left d hprod).trans
    (Nat.le_of_dvd hn (smooth_divisor_large_prime_product_dvd Y n d hdY hdn))

lemma largePrimeDivisors_card_lt_of_smooth_divisor (Y n d s : ℕ) (hY : 1 ≤ Y)
    (hn : 0 < n) (hdY : d ∈ Nat.smoothNumbers Y) (hdn : d ∣ n) (hN : n < d * Y ^ s) :
    (largePrimeDivisors Y n).card < s := by
  by_contra h
  have hs : s ≤ (largePrimeDivisors Y n).card := by omega
  have hpow := Nat.pow_le_pow_right (by omega : 0 < Y) hs
  have hlo := smooth_divisor_large_prime_power_le Y n d hn hdY hdn
  have h := Nat.mul_le_mul_left d hpow
  omega

noncomputable def binomialSievePartial (n k : ℕ) : ℝ :=
  ∑ j ∈ range (k + 1), (-1 : ℝ)^j * (n.choose j : ℝ)

lemma binomialSievePartial_zero (k : ℕ) : binomialSievePartial 0 k = 1 := by
  unfold binomialSievePartial
  simp [Nat.choose_zero_succ, sum_range_succ']

lemma binomialSievePartial_succ (n k : ℕ) :
    binomialSievePartial (n + 1) k = (-1 : ℝ)^k * (n.choose k : ℝ) := by
  unfold binomialSievePartial
  exact_mod_cast (Int.alternating_sum_range_choose_eq_choose (n := n) (m := k))

lemma binomialSievePartial_eq_indicator (n k : ℕ) (hnk : n ≤ k) :
    binomialSievePartial n k = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp only [binomialSievePartial_zero, if_true]
  | succ n =>
    rw [binomialSievePartial_succ, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
    simp

lemma binomialSievePartial_odd_le (n k : ℕ) :
    binomialSievePartial n (2 * k + 1) ≤ if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp only [binomialSievePartial_zero, if_true, le_refl]
  | succ n =>
    rw [binomialSievePartial_succ, show (-1 : ℝ)^(2 * k + 1) = -1 by simp [pow_add, pow_mul], if_neg (by omega)]
    have h := Nat.cast_nonneg (α := ℝ) (n.choose (2 * k + 1))
    linarith

lemma binomialSievePartial_even_ge (n k : ℕ) :
    (if n = 0 then (1 : ℝ) else 0) ≤ binomialSievePartial n (2 * k) := by
  cases n with
  | zero => simp only [binomialSievePartial_zero, if_true, le_refl]
  | succ n =>
    rw [binomialSievePartial_succ, show (-1 : ℝ)^(2 * k) = 1 by simp [pow_mul], if_neg (by omega), one_mul]
    exact Nat.cast_nonneg _

noncomputable def largePrimeMoment (P : Finset ℕ) (w : ℕ → ℝ) (Y j : ℕ) : ℝ :=
  ∑ p ∈ P, w p * ((largePrimeDivisors Y (p - 1)).card.choose j : ℝ)

noncomputable def largePrimeSievePartial (P : Finset ℕ) (w : ℕ → ℝ) (Y k : ℕ) : ℝ :=
  ∑ j ∈ range (k + 1), (-1 : ℝ)^j * largePrimeMoment P w Y j

lemma largePrimeSievePartial_eq_pointwise (P : Finset ℕ) (w : ℕ → ℝ) (Y k : ℕ) :
    largePrimeSievePartial P w Y k =
      ∑ p ∈ P, w p * binomialSievePartial (largePrimeDivisors Y (p - 1)).card k := by
  unfold largePrimeSievePartial largePrimeMoment binomialSievePartial
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro j hj
  ring

lemma smooth_prime_weight_eq_indicator (P : Finset ℕ) (w : ℕ → ℝ) (Y : ℕ)
    (hP : ∀ p ∈ P, 2 ≤ p) :
    (∑ p ∈ P.filter (fun p => p - 1 ∈ Nat.smoothNumbers Y), w p) =
      ∑ p ∈ P, w p * (if (largePrimeDivisors Y (p - 1)).card = 0 then 1 else 0) := by
  rw [sum_filter]
  apply sum_congr rfl
  intro p hp
  simp only [largePrimeDivisors_card_zero_iff Y (p - 1) (by have := hP p hp; omega)]
  split_ifs <;> simp

/-- Exact inclusion-exclusion when every predecessor has at most k distinct
large prime divisors. -/
theorem smooth_prime_weight_eq_large_moments (P : Finset ℕ) (w : ℕ → ℝ) (Y k : ℕ)
    (hP : ∀ p ∈ P, 2 ≤ p)
    (hcard : ∀ p ∈ P, (largePrimeDivisors Y (p - 1)).card ≤ k) :
    (∑ p ∈ P.filter (fun p => p - 1 ∈ Nat.smoothNumbers Y), w p) =
      largePrimeSievePartial P w Y k := by
  rw [smooth_prime_weight_eq_indicator P w Y hP, largePrimeSievePartial_eq_pointwise]
  exact sum_congr rfl (fun p hp => by rw [binomialSievePartial_eq_indicator _ _ (hcard p hp)])

/-- The odd truncations give lower bounds, and the even truncations upper
bounds, provided the prime weights are nonnegative. -/
theorem smooth_prime_weight_bonferroni (P : Finset ℕ) (w : ℕ → ℝ) (Y k : ℕ)
    (hP : ∀ p ∈ P, 2 ≤ p) (hw : ∀ p ∈ P, 0 ≤ w p) :
    largePrimeSievePartial P w Y (2 * k + 1) ≤
      (∑ p ∈ P.filter (fun p => p - 1 ∈ Nat.smoothNumbers Y), w p) ∧
    (∑ p ∈ P.filter (fun p => p - 1 ∈ Nat.smoothNumbers Y), w p) ≤
      largePrimeSievePartial P w Y (2 * k) := by
  rw [smooth_prime_weight_eq_indicator P w Y hP,
    largePrimeSievePartial_eq_pointwise, largePrimeSievePartial_eq_pointwise]
  constructor
  · exact sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left (binomialSievePartial_odd_le _ _) (hw p hp))
  · exact sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left (binomialSievePartial_even_ge _ _) (hw p hp))

/-- Below d*Y^2 a Y-smooth divisor d leaves at most one large prime factor.
Here the first-moment subtraction is exact, not merely an upper-sieve cover. -/
theorem smooth_prime_weight_eq_first_moment (P : Finset ℕ) (w : ℕ → ℝ) (Y : ℕ)
    (hY : 1 ≤ Y) (hP : ∀ p ∈ P, 2 ≤ p)
    (hdiv : ∀ p ∈ P, ∃ d, d ∈ Nat.smoothNumbers Y ∧ d ∣ p - 1 ∧ p - 1 < d * Y^2) :
    (∑ p ∈ P.filter (fun p => p - 1 ∈ Nat.smoothNumbers Y), w p) =
      largePrimeMoment P w Y 0 - largePrimeMoment P w Y 1 := by
  rw [smooth_prime_weight_eq_large_moments P w Y 1 hP (by
    intro p hp
    obtain ⟨d, hdY, hdn, hN⟩ := hdiv p hp
    have h := largePrimeDivisors_card_lt_of_smooth_divisor Y (p - 1) d 2 hY
      (by have := hP p hp; omega) hdY hdn hN
    omega)]
  simp only [largePrimeSievePartial, sum_range_succ, sum_range_zero, zero_add, pow_zero,
    pow_one, one_mul, neg_one_mul, sub_eq_add_neg]

end Erdos821
