import Submission.SignedSmoothMinorant

/-! A finite two-scale minorant for the Mangoldt pair product. Its validity
window is t log n <= 1/4 in both coordinates. No positive mean in that
moving-parameter window is proved here. -/
namespace Erdos972TwoScalePairMinorant

open Finset ArithmeticFunction
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive
open Erdos972SharpSmoothMangoldt Erdos972SignedSmoothMinorant
open Erdos972PrimePowerError

set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma doubling_product_lower {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn0 : n ≠ 0) (hn1 : n ≠ 1) (hn : ¬ IsPrimePow n) :
    4-2*t*Real.log n ≤ ∏ p ∈ n.primeFactors, (1+Real.exp (-t*Real.log p)) := by
  classical
  have hc0 : 0 < n.primeFactors.card := card_pos.mpr
    (Nat.nonempty_primeFactors.mpr (by omega))
  have hc1 : n.primeFactors.card ≠ 1 := fun h =>
    hn (isPrimePow_iff_card_primeFactors_eq_one.mpr h)
  obtain ⟨p, hp, q, hq, hpq⟩ := one_lt_card.mp (show 1 < n.primeFactors.card by omega)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hpqd : p*q ∣ n := ((Nat.coprime_primes hpp hqp).mpr hpq).mul_dvd_of_dvd_of_dvd
    (Nat.dvd_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hq)
  have hlogs : Real.log p+Real.log q ≤ Real.log n := by
    have hh := Real.log_le_log (Nat.cast_pos.mpr (Nat.mul_pos hpp.pos hqp.pos))
      (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpqd))
    rwa [Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hpp.ne_zero)
      (Nat.cast_ne_zero.mpr hqp.ne_zero)] at hh
  have hm := mul_le_mul_of_nonneg_left hlogs ht.le
  have he := Real.add_one_le_exp (-t*Real.log p)
  have hf := Real.add_one_le_exp (-t*Real.log q)
  have hg := Real.add_one_le_exp ((-t*Real.log p)+(-t*Real.log q))
  rw [Real.exp_add] at hg
  have hpair : 4-2*t*Real.log n ≤
      (1+Real.exp (-t*Real.log p))*(1+Real.exp (-t*Real.log q)) := by
    nlinarith only [hm, he, hf, hg]
  have hqe : q ∈ n.primeFactors.erase p := mem_erase.mpr ⟨hpq.symm, hq⟩
  rw [← prod_erase_mul n.primeFactors (fun r : ℕ => 1+Real.exp (-t*Real.log r)) hp,
    ← prod_erase_mul (n.primeFactors.erase p) (fun r : ℕ => 1+Real.exp (-t*Real.log r)) hqe]
  have hrest : 1 ≤ ∏ r ∈ (n.primeFactors.erase p).erase q,
      (1+Real.exp (-t*Real.log r)) :=
    one_le_prod _ (fun r => by linarith only [Real.exp_nonneg (-t*Real.log r)])
  have hh := mul_le_mul_of_nonneg_right hrest
    (mul_nonneg (by positivity : 0 ≤ 1+Real.exp (-t*Real.log p))
      (by positivity : 0 ≤ 1+Real.exp (-t*Real.log q)))
  nlinarith only [hh, hpair]

lemma smooth_primePower_formula {t : ℝ} {n : ℕ} (hn : IsPrimePow n) :
    smoothMangoldt t n = (1-Real.exp (-t*Λ n))/t := by
  have hn1 := hn.ne_one
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
  rw [smoothMangoldt, expDivisorSum_at_zero, one_apply, if_neg hn1, sub_zero,
    expDivisorSum_prime_pow t hp hk, vonMangoldt_apply_pow hk.ne',
    vonMangoldt_apply_prime hp]

lemma smooth_primePower_double {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : IsPrimePow n) :
    smoothMangoldt (2*t) n = smoothMangoldt t n*(1+Real.exp (-t*Λ n))/2 := by
  rw [smooth_primePower_formula hn, smooth_primePower_formula hn, exp_double]
  field_simp
  ring

noncomputable def lowerWeight (t : ℝ) (n : ℕ) : ℝ :=
  2*smoothMangoldt t n-(8/7)*smoothMangoldt (2*t) n

noncomputable def upperWeight (t : ℝ) (n : ℕ) : ℝ := (4/3)*smoothMangoldt t n

lemma upperWeight_nonneg {t : ℝ} (ht : 0 < t) (n : ℕ) : 0 ≤ upperWeight t n := by
  exact mul_nonneg (by norm_num) (smoothMangoldt_nonneg ht n)

/-- Genuine lower and upper weights, not just formal expected means. -/
theorem two_scale_sandwich {t : ℝ} (ht : 0 < t) (n : ℕ)
    (hsmall : t*Real.log n ≤ 1/4) :
    lowerWeight t n ≤ Λ n ∧ Λ n ≤ upperWeight t n := by
  by_cases hn : IsPrimePow n
  · have hΛ := vonMangoldt_nonneg (n := n)
    have hΛsmall : t*Λ n ≤ 1/4 :=
      (mul_le_mul_of_nonneg_left vonMangoldt_le_log ht.le).trans hsmall
    have hS := smoothMangoldt_nonneg ht n
    have hSupper := smoothMangoldt_primePower_le ht hn
    have herror := exp_slope_error ht hΛ
    rw [← smooth_primePower_formula hn] at herror
    have hquad := mul_le_mul_of_nonneg_right hΛsmall hΛ
    have he : 3/4 ≤ Real.exp (-t*Λ n) := by
      linarith only [Real.add_one_le_exp (-t*Λ n), hΛsmall]
    have hdouble : (7/8)*smoothMangoldt t n ≤ smoothMangoldt (2*t) n := by
      rw [smooth_primePower_double ht hn]
      have hh := mul_le_mul_of_nonneg_left he hS
      nlinarith only [hh]
    constructor
    · unfold lowerWeight
      linarith only [hdouble, hSupper]
    · unfold upperWeight
      have he' := (abs_le.mp herror).1
      nlinarith only [he', hquad]
  · refine ⟨?_, ?_⟩
    · rw [vonMangoldt_eq_zero_iff.mpr hn]
      by_cases hn0 : n = 0
      · simp [hn0, lowerWeight, smoothMangoldt, expDivisorSum]
      by_cases hn1 : n = 1
      · simp [hn1, lowerWeight, smoothMangoldt, expDivisorSum]
      have hp := doubling_product_lower ht hn0 hn1 hn
      have hp' : (7/2:ℝ) ≤ ∏ p ∈ n.primeFactors, (1+Real.exp (-t*Real.log p)) := by
        linarith only [hp, hsmall]
      have he := mul_le_mul_of_nonneg_left hp' (expDivisorSum_nonneg ht.le n)
      rw [← expDivisorSum_double t hn0] at he
      have hdouble : (7/4)*smoothMangoldt t n ≤ smoothMangoldt (2*t) n := by
        rw [smoothMangoldt, smoothMangoldt, expDivisorSum_at_zero,
          one_apply, if_neg hn1, sub_zero, sub_zero]
        apply (le_div_iff₀ (show 0 < 2*t by positivity)).mpr
        have htn : t ≠ 0 := ht.ne'
        field_simp
        simp only [mul_comm t 2]
        nlinarith only [he]
      unfold lowerWeight
      linarith only [hdouble]
    · rw [vonMangoldt_eq_zero_iff.mpr hn]
      exact upperWeight_nonneg ht n

lemma product_minorant {x y l r U V : ℝ}
    (hl : l ≤ x) (hr : r ≤ y) (hxU : x ≤ U) (hyV : y ≤ V)
    (hU : 0 ≤ U) (hV : 0 ≤ V) :
    l*V+U*r-U*V ≤ x*y := by
  have h₁ := mul_le_mul_of_nonneg_right hl hV
  have h₂ := mul_le_mul_of_nonneg_left hr hU
  have h₃ := mul_nonneg (sub_nonneg.mpr hxU) (sub_nonneg.mpr hyV)
  nlinarith only [h₁, h₂, h₃]

noncomputable def pairMinorant (t : ℝ) (m n : ℕ) : ℝ :=
  (32/63)*(7*smoothMangoldt t m*smoothMangoldt t n-
    3*(smoothMangoldt (2*t) m*smoothMangoldt t n+
      smoothMangoldt t m*smoothMangoldt (2*t) n))

/-- This signed two-scale expression is a pointwise minorant for the pair
product under a fixed numerical parameter margin. -/
theorem pairMinorant_le {t : ℝ} (ht : 0 < t) (m n : ℕ)
    (hm : t*Real.log m ≤ 1/4) (hn : t*Real.log n ≤ 1/4) :
    pairMinorant t m n ≤ Λ m*Λ n := by
  obtain ⟨hl, hU⟩ := two_scale_sandwich ht m hm
  obtain ⟨hr, hV⟩ := two_scale_sandwich ht n hn
  have hh := product_minorant hl hr hU hV (upperWeight_nonneg ht m) (upperWeight_nonneg ht n)
  calc
    _ = lowerWeight t m*upperWeight t n+upperWeight t m*lowerWeight t n-
        upperWeight t m*upperWeight t n := by
      unfold pairMinorant lowerWeight upperWeight
      ring
    _ ≤ _ := hh

noncomputable def pairMinorantSum (t α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, pairMinorant t n (floorMul α n)

/-- The actual floor-map comparison, with a single endpoint condition.
No positive lower bound for pairMinorantSum is included. -/
theorem pairMinorantSum_le {α t : ℝ} (hα : 1 ≤ α) (ht : 0 < t) (N : ℕ)
    (hsmall : t*Real.log (floorMul α N) ≤ 1/4) :
    pairMinorantSum t α N ≤ mangoldtCorrelation α N := by
  unfold pairMinorantSum mangoldtCorrelation
  apply sum_le_sum
  intro n hn
  have hn0 := (mem_Ioc.mp hn).1
  have hnN := (mem_Ioc.mp hn).2
  have hgn := floorMul_pos hα hn0
  have hngN : n ≤ floorMul α N := hnN.trans (self_le_floorMul hα N)
  have hggN : floorMul α n ≤ floorMul α N := (floorMul_strictMono hα).monotone hnN
  apply pairMinorant_le ht
  · exact (mul_le_mul_of_nonneg_left
      (Real.log_le_log (Nat.cast_pos.mpr hn0) (Nat.cast_le.mpr hngN)) ht.le).trans hsmall
  · exact (mul_le_mul_of_nonneg_left
      (Real.log_le_log (Nat.cast_pos.mpr hgn) (Nat.cast_le.mpr hggN)) ht.le).trans hsmall

#print axioms two_scale_sandwich
#print axioms pairMinorant_le
#print axioms pairMinorantSum_le

end Erdos972TwoScalePairMinorant
