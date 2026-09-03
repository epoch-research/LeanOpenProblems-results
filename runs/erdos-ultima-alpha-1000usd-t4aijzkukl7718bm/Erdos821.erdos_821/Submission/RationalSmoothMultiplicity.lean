import Submission.StrictSquareRootReciprocal

/-!
# Sharp limiting transfer from rational smoothness to totient multiplicity

Reciprocal divergence at the fixed relative smoothness exponent b/a supplies
every multiplicity exponent below 1-b/a. The strict inequality absorbs the
finite losses in the dyadic pigeonhole bound by rescaling. No assertion at
arbitrarily small b/a is proved here.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

lemma rational_smooth_prime_mem_dyadic_smooth {a b k L p : ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (hp : p ∈ rationalSmoothShiftedPrimes a b)
    (hpbound : p < 2 ^ (a * k * L)) :
    p - 1 ∈ Nat.smoothNumbers (2 ^ (b * k * L)) := by
  apply Nat.mem_smoothNumbers'.mpr
  intro q hq hqd
  have hp0 : p - 1 ≠ 0 := by have := hp.1.two_le; omega
  have hqmem : q ∈ (p - 1).primeFactors := hq.mem_primeFactors hqd hp0
  have hpower : q ^ a < (2 ^ (b * k * L)) ^ a := by
    calc
      q ^ a ≤ (p - 1) ^ b := hp.2 q hqmem
      _ < (2 ^ (a * k * L)) ^ b :=
        (Nat.pow_lt_pow_iff_left hb.ne').mpr (by omega)
      _ = _ := by rw [← pow_mul, ← pow_mul]; congr 1; ring
  exact (Nat.pow_lt_pow_iff_left ha.ne').mp hpower

lemma rational_reciprocal_supplies_dyadic_family (a b k : ℕ)
    (hb : 0 < b) (hba : b < a) (hk : 1 ≤ k)
    (H : ¬Summable ((rationalSmoothShiftedPrimes a b).indicator
      (fun p : ℕ => 1 / (p : ℝ)))) (M : ℕ) :
    ∃ L : ℕ, M ≤ L ∧ ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (a * k * L) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ (b * k * L))) ∧
      2 ^ ((a * k - 1) * L) ≤ P.card := by
  have ha : 0 < a := hb.trans hba
  have ht : 0 < a * k := Nat.mul_pos ha (by omega)
  have hsum : ¬Summable ((rationalSmoothShiftedPrimes a b).indicator
      (fun p : ℕ => (p : ℝ) ^ (-(1 : ℝ)))) := by
    simpa only [Real.rpow_neg_one, one_div] using H
  have hexp : ((a * k - 1 : ℕ) : ℝ) < (a * k : ℕ) * (1 : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ a * k), Nat.cast_one, mul_one]
    linarith
  obtain ⟨L, hML, hcount⟩ := exists_large_dyadic_count_of_not_summable
    (rationalSmoothShiftedPrimes a b) (a * k) (a * k - 1) 1 ht
    (by norm_num) hexp hsum M
  let P := (Finset.range (2 ^ (a * k * L))).filter
    (fun p => p ∈ rationalSmoothShiftedPrimes a b)
  refine ⟨L, hML, P, ?_, hcount⟩
  intro p hp
  obtain ⟨hpL, hpS⟩ := Finset.mem_filter.mp hp
  have hpbound := Finset.mem_range.mp hpL
  exact ⟨hpS.1, hpbound.le,
    rational_smooth_prime_mem_dyadic_smooth ha hb hpS hpbound⟩

/-- Rescaling removes every fixed exponent loss, but does not change the
underlying relative smoothness exponent. -/
theorem infinite_g_gt_of_rational_smooth_reciprocal (a b : ℕ)
    (hb : 0 < b) (hba : b < a)
    (H : ¬Summable ((rationalSmoothShiftedPrimes a b).indicator
      (fun p : ℕ => 1 / (p : ℝ))))
    (γ : ℝ) (hγ : γ < 1 - (b : ℝ) / a) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ γ}.Infinite := by
  have ha : 0 < a := hb.trans hba
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hγ' : γ < ((a : ℝ) - b) / a := by
    convert hγ using 1
    field_simp
  have hmargin : 0 < (a : ℝ) - b - a * γ := by
    have h := (lt_div_iff₀ haR).mp hγ'
    nlinarith only [h]
  obtain ⟨k, hk⟩ := exists_nat_gt (max 4 (3 / ((a : ℝ) - b - a * γ)))
  have hk4R : (4 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hk4 : 4 ≤ k := by exact_mod_cast hk4R.le
  have h3 : 3 < (k : ℝ) * ((a : ℝ) - b - a * γ) :=
    (div_lt_iff₀ hmargin).mp ((le_max_right _ _).trans_lt hk)
  have hgap : b * k + 4 ≤ a * k := by
    have h := Nat.mul_le_mul_right k (show b + 1 ≤ a by omega)
    nlinarith only [h, hk4]
  have hinf := infinite_g_gt_of_general_dyadic_density (a * k) (a * k - 1) (b * k)
    (by omega) (by omega) (by omega)
    (rational_reciprocal_supplies_dyadic_family a b k hb hba (by omega) H)
  have hnum : ((a * k - 1 - b * k - 2 : ℕ) : ℝ) =
      (a : ℝ) * k - b * k - 3 := by
    rw [Nat.cast_sub (by omega : 2 ≤ a * k - 1 - b * k),
      Nat.cast_sub (by omega : b * k ≤ a * k - 1),
      Nat.cast_sub (by omega : 1 ≤ a * k), Nat.cast_mul, Nat.cast_mul]
    norm_num
    ring
  have hakR : (0 : ℝ) < (a * k : ℕ) := by
    exact_mod_cast Nat.mul_pos ha (by omega : 0 < k)
  have hγk : γ < ((a * k - 1 - b * k - 2 : ℕ) : ℝ) / (a * k : ℕ) := by
    apply (lt_div_iff₀ hakR).mpr
    rw [hnum, Nat.cast_mul]
    nlinarith only [h3]
  apply (hinf.diff (Set.finite_singleton 0)).mono
  intro n hn
  have hn0 : n ≠ 0 := by simpa only [Set.mem_singleton_iff] using hn.2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  exact (Real.rpow_le_rpow_of_exponent_le hn1 hγk.le).trans_lt hn.1

/-- The strict square-root sieve result gives all exponents below the
complementary rational threshold, not just one selected approximant. -/
theorem infinite_g_gt_strict_square_root_limit (r : ℕ) (hr : 1 ≤ r)
    (hC : 150994944 * Sieve.totientRatioAverageConstant ≤ (r : ℝ))
    (γ : ℝ) (hγ : γ < 1 / 2 + 1 / (64 * (r : ℝ) - 1)) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ γ}.Infinite := by
  apply infinite_g_gt_of_rational_smooth_reciprocal (128 * r - 2) (64 * r - 3)
    (by omega) (by omega) (strict_square_root_prime_reciprocal_divergence r hr hC) γ
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hden : 64 * (r : ℝ) - 1 ≠ 0 := by linarith
  have heq : 1 - ((64 * r - 3 : ℕ) : ℝ) / ((128 * r - 2 : ℕ) : ℝ) =
      1 / 2 + 1 / (64 * (r : ℝ) - 1) := by
    rw [Nat.cast_sub (by omega : 3 ≤ 64 * r),
      Nat.cast_sub (by omega : 2 ≤ 128 * r)]
    push_cast
    rw [show 128 * (r : ℝ) - 2 = 2 * (64 * (r : ℝ) - 1) by ring]
    field_simp
    ring
  rw [heq]
  exact hγ

end Erdos821
