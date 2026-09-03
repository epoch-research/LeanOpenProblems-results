import Submission.CompositeBelowHalfScales
import Submission.SmoothModulusMoments

/-!
# Primes with many prescribed block-prime factors in their predecessors

The below-square-root composite-modulus estimate is converted into a
prime-count lower bound. The prime-power error is controlled by the same
constant incidence bound as the prime overcount, rather than by the number
of moduli.
-/

open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators

namespace Erdos821

open AnalyticSieve

set_option maxHeartbeats 2000000

noncomputable def structuredWitnessPrimes (r m N : ℕ) : Finset ℕ :=
  (N + 1).primesBelow.filter (fun p => r ≤ (blockPrimeDivisors m (p - 1)).card)

lemma prime_product_divisor_count_le_choose (r t m n : ℕ) (hm : 1 ≤ m)
    (hn : 0 < n) (hN : n < 2 ^ (64 * t * m)) :
    ((primeProductModuli r m).filter (fun d => d ∣ n)).card ≤ (t - 1).choose r := by
  rw [prime_product_divisor_count_eq_choose]
  have h := block_prime_divisor_card_lt t m n hm hn hN
  exact Nat.choose_le_choose r (by omega)

lemma sum_product_progressions_eq_incidence (r m N : ℕ) :
    (∑ d ∈ primeProductModuli r m, residueOneMangoldt d N) =
      ∑ n ∈ Icc 1 N,
        (((primeProductModuli r m).filter (fun d => d ∣ n - 1)).card : ℝ) * vonMangoldt n := by
  simp only [residueOneMangoldt]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  simp only [residue_one_iff_dvd_pred (mem_Icc.mp hn).1]
  rw [← sum_filter, sum_const, nsmul_eq_mul]

/-- The incidence bound applies also to proper prime powers. -/
theorem product_progression_weight_le_structured_count (r t m : ℕ) (hm : 1 ≤ m) :
    (∑ d ∈ primeProductModuli r m, residueOneMangoldt d (2 ^ (64 * t * m))) ≤
      (((t - 1).choose r : ℕ) : ℝ) * Real.log (2 ^ (64 * t * m) : ℕ) *
        (((structuredWitnessPrimes r m (2 ^ (64 * t * m))).card : ℝ) +
          2 * Real.sqrt (2 ^ (64 * t * m) : ℕ)) := by
  let N := 2 ^ (64 * t * m)
  let C : ℝ := ((t - 1).choose r : ℕ)
  let G := structuredWitnessPrimes r m N
  let I (n : ℕ) : ℕ := ((primeProductModuli r m).filter (fun d => d ∣ n - 1)).card
  have hN : 1 ≤ N := Nat.one_le_of_lt (by dsimp [N]; positivity)
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg _
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      (I n : ℝ) * vonMangoldt n ≤
        (if n ∈ G then C * Real.log N else 0) +
        (if ¬n.Prime then C * vonMangoldt n else 0) := by
    have hnN := (mem_Icc.mp hn).2
    by_cases hn1 : n = 1
    · subst n
      simp only [vonMangoldt_apply_one, mul_zero, ite_self, add_zero]
      split_ifs <;> first | exact mul_nonneg hC hlog | exact le_rfl
    have hn2 : 2 ≤ n := by have := (mem_Icc.mp hn).1; omega
    have hinc : (I n : ℝ) ≤ C := by
      dsimp only [I, C]
      exact_mod_cast prime_product_divisor_count_le_choose r t m (n - 1) hm (by omega) (by dsimp [N] at hnN; omega)
    have hwt := mul_le_mul_of_nonneg_right hinc (vonMangoldt_nonneg (n := n))
    by_cases hp : n.Prime
    · rw [if_neg (not_not.mpr hp)]
      by_cases hnG : n ∈ G
      · rw [if_pos hnG, add_zero]
        exact hwt.trans (mul_le_mul_of_nonneg_left (vonMangoldt_le_log.trans (log_nat_mono hnN)) hC)
      · have hlt : (blockPrimeDivisors m (n - 1)).card < r := by
          by_contra h
          apply hnG
          exact mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega, hp⟩, by omega⟩
        have hzero : I n = 0 := by
          dsimp [I]
          rw [prime_product_divisor_count_eq_choose]
          exact Nat.choose_eq_zero_of_lt hlt
        simp only [if_neg hnG, hzero, Nat.cast_zero, zero_mul, add_zero, le_refl]
    · rw [if_pos hp]
      split_ifs <;> linarith [mul_nonneg hC hlog]
  have hG : (Icc 1 N).filter (fun n => n ∈ G) = G := by
    ext n
    simp only [mem_filter]
    constructor
    · exact fun h => h.2
    · intro hn
      have hp := (Nat.mem_primesBelow.mp (mem_filter.mp hn).1)
      exact ⟨mem_Icc.mpr ⟨hp.2.pos, by omega⟩, hn⟩
  calc
    _ = ∑ n ∈ Icc 1 N, (I n : ℝ) * vonMangoldt n := sum_product_progressions_eq_incidence r m N
    _ ≤ ∑ n ∈ Icc 1 N,
        ((if n ∈ G then C * Real.log N else 0) +
          (if ¬n.Prime then C * vonMangoldt n else 0)) := sum_le_sum hpoint
    _ = (G.card : ℝ) * (C * Real.log N) +
        C * ∑ n ∈ (Icc 1 N).filter (fun n => ¬n.Prime), vonMangoldt n := by
      rw [sum_add_distrib]
      simp only [← sum_filter, hG, sum_const, nsmul_eq_mul, ← mul_sum]
    _ ≤ (G.card : ℝ) * (C * Real.log N) + C * (2 * Real.sqrt N * Real.log N) :=
      _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left (mangoldt_nonprime_sum_le N hN) hC)
    _ = _ := by dsimp only [G, C, N]; ring

theorem eventually_product_mangoldt_weight_lower (r t : ℕ) (hrt : 2 * r + 1 ≤ t) :
    ∀ᶠ m : ℕ in atTop,
      (progressionScaleN (t * m) : ℝ) /
        (16 * (primeProductMassConstant r : ℝ) * ((m : ℝ) + 1) ^ r) ≤
          ∑ d ∈ primeProductModuli r m, residueOneMangoldt d (progressionScaleN (t * m)) := by
  filter_upwards [eventually_product_mangoldt_total_lower r t (r + 1) hrt,
    eventually_nat_poly_le_two_pow 1 (4096 * r) 1,
    eventually_ge_atTop (max 1 (16 * primeProductMassConstant r))] with m htotal hsmall hm
  let N := progressionScaleN (t * m)
  let C : ℝ := primeProductMassConstant r
  let z : ℝ := (m : ℝ) + 1
  have hC : 0 < C := by dsimp [C]; exact_mod_cast primeProductMassConstant_pos r
  have hz : 0 < z := by dsimp [z]; positivity
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hsmall' : 4096 * r * (m + 1) ≤ progressionScaleN m := by
    have hpow : 2 ^ m ≤ progressionScaleN m := Nat.pow_le_pow_right (by decide) (by omega)
    simpa only [one_mul, pow_one] using hsmall.trans hpow
  have hmass : 1 / (C * z ^ r) ≤ primeProductReciprocalMass r m :=
    primeProductModuli_reciprocal_lower r m hsmall'
  have htm : 1 ≤ t * m := Nat.mul_pos (by omega) (by omega)
  have hpsi : (N : ℝ) / 8 ≤ mangoldtSum N := progression_scale_mangoldt_lower htm
  have hmain : (N : ℝ) / (8 * C * z ^ r) ≤ mangoldtSum N * primeProductReciprocalMass r m := by
    calc
      _ = ((N : ℝ) / 8) * (1 / (C * z ^ r)) := by ring
      _ ≤ _ := mul_le_mul hpsi hmass (by positivity) (by
        exact hpsi.trans' (div_nonneg hN (by norm_num)))
  have hbudget : 16 * C ≤ z := by
    have hm' : 16 * primeProductMassConstant r ≤ m + 1 := by omega
    dsimp only [C, z]
    exact_mod_cast hm'
  have herr : (N : ℝ) / z ^ (r + 1) ≤ (N : ℝ) / (16 * C * z ^ r) := by
    apply div_le_div_of_nonneg_left hN (by positivity)
    rw [pow_succ]
    have h := mul_le_mul_of_nonneg_right hbudget (pow_nonneg hz.le r)
    nlinarith only [h]
  have heq : (N : ℝ) / (8 * C * z ^ r) = 2 * ((N : ℝ) / (16 * C * z ^ r)) := by ring
  change mangoldtSum N * primeProductReciprocalMass r m - (N : ℝ) / z ^ (r + 1) ≤ _ at htotal
  change (N : ℝ) / (16 * C * z ^ r) ≤ _
  linarith only [hmain, herr, heq, htotal]

def structuredPrimeCountConstant (r t : ℕ) : ℕ :=
  2048 * primeProductMassConstant r * t * (t - 1).choose r

lemma structured_prime_count_of_weight (r t m : ℕ) (_ht : 1 ≤ t) (hm : 1 ≤ m)
    (hweight : (progressionScaleN (t * m) : ℝ) /
      (16 * (primeProductMassConstant r : ℝ) * ((m : ℝ) + 1) ^ r) ≤
        ∑ d ∈ primeProductModuli r m, residueOneMangoldt d (progressionScaleN (t * m)))
    (hpoly : 4096 * (t - 1).choose r * primeProductMassConstant r * t * (m + 1) ^ (r + 1) ≤
      2 ^ (32 * t * m)) :
    progressionScaleN (t * m) ≤ structuredPrimeCountConstant r t * (m + 1) ^ (r + 1) *
      (structuredWitnessPrimes r m (progressionScaleN (t * m))).card := by
  let N := progressionScaleN (t * m)
  let C : ℝ := primeProductMassConstant r
  let B : ℝ := ((t - 1).choose r : ℕ)
  let z : ℝ := (m : ℝ) + 1
  let R : ℝ := Real.sqrt N
  let G := structuredWitnessPrimes r m N
  have hC : 0 < C := by dsimp [C]; exact_mod_cast primeProductMassConstant_pos r
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have hz : 0 < z := by dsimp [z]; positivity
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R * R = (N : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hlog : Real.log (N : ℝ) ≤ 64 * (t : ℝ) * z := by
    have h := log_two_pow_le (64 * (t * m))
    change Real.log (N : ℝ) ≤ _ at h
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    dsimp [z]
    nlinarith [Nat.cast_nonneg (α := ℝ) t]
  have hpolyR : 4096 * B * C * t * z ^ (r + 1) ≤ R := by
    dsimp only [R, N]
    rw [sqrt_progressionScaleN]
    have h : (4096 : ℝ) * ((t - 1).choose r : ℕ) * primeProductMassConstant r * t *
        ((m : ℝ) + 1) ^ (r + 1) ≤ (2 : ℝ) ^ (32 * t * m) := by exact_mod_cast hpoly
    simpa only [mul_assoc] using h
  have hupper : (∑ d ∈ primeProductModuli r m, residueOneMangoldt d N) ≤
      B * Real.log N * ((G.card : ℝ) + 2 * R) := by
    simpa only [N, progressionScaleN, mul_assoc, G, R, B] using
      product_progression_weight_le_structured_count r t m hm
  have herr : 2 * B * R * Real.log N ≤ (N : ℝ) / (32 * C * z ^ r) := by
    apply (le_div_iff₀ (by positivity : 0 < 32 * C * z ^ r)).mpr
    calc
      _ ≤ (2 * B * R * (64 * (t : ℝ) * z)) * (32 * C * z ^ r) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by positivity)) (by positivity)
      _ = (4096 * B * C * t * z ^ (r + 1)) * R := by rw [pow_succ]; ring
      _ ≤ R * R := mul_le_mul_of_nonneg_right hpolyR hR
      _ = _ := hR2
  have heq : (N : ℝ) / (16 * C * z ^ r) = 2 * ((N : ℝ) / (32 * C * z ^ r)) := by ring
  change (N : ℝ) / (16 * C * z ^ r) ≤ _ at hweight
  have hgood : (N : ℝ) / (32 * C * z ^ r) ≤ B * Real.log N * (G.card : ℝ) := by
    nlinarith only [hweight, hupper, herr, heq]
  have hgood' : (N : ℝ) / (32 * C * z ^ r) ≤ B * (64 * (t : ℝ) * z) * (G.card : ℝ) :=
    hgood.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hB) (Nat.cast_nonneg _))
  have hfinal := (div_le_iff₀ (by positivity : 0 < 32 * C * z ^ r)).mp hgood'
  have hfinal' : (N : ℝ) ≤ (structuredPrimeCountConstant r t : ℝ) * z ^ (r + 1) * (G.card : ℝ) := by
    dsimp only [structuredPrimeCountConstant]
    simp only [Nat.cast_mul, Nat.cast_ofNat, pow_succ]
    dsimp only [C, B] at hfinal
    nlinarith only [hfinal]
  dsimp only [N, G, z] at hfinal'
  exact_mod_cast hfinal'

/-- A prime-count-sized family with r distinct prime factors in the prescribed
small block. Its density loses only a fixed power of the logarithm. -/
theorem eventually_structured_prime_count (r t : ℕ) (hrt : 2 * r + 1 ≤ t) :
    ∀ᶠ m : ℕ in atTop,
      progressionScaleN (t * m) ≤ structuredPrimeCountConstant r t * (m + 1) ^ (r + 1) *
        (structuredWitnessPrimes r m (progressionScaleN (t * m))).card := by
  filter_upwards [eventually_product_mangoldt_weight_lower r t hrt,
    eventually_nat_poly_le_two_pow 1 (4096 * (t - 1).choose r * primeProductMassConstant r * t) (r + 1),
    eventually_ge_atTop 1] with m hweight hpoly hm
  apply structured_prime_count_of_weight r t m (by omega) hm hweight
  have hpow : 2 ^ m ≤ 2 ^ (32 * t * m) :=
    Nat.pow_le_pow_right (by decide) (by nlinarith)
  simpa only [one_mul] using hpoly.trans hpow

lemma structuredWitnessPrimes_has_divisor {r m N p : ℕ}
    (hp : p ∈ structuredWitnessPrimes r m N) :
    p.Prime ∧ p ≤ N ∧ ∃ d ∈ primeProductModuli r m, d ∣ p - 1 := by
  obtain ⟨hpP, hcard⟩ := mem_filter.mp hp
  have hpdata := Nat.mem_primesBelow.mp hpP
  have hcount : 0 < ((primeProductModuli r m).filter (fun d => d ∣ p - 1)).card := by
    rw [prime_product_divisor_count_eq_choose]
    exact Nat.choose_pos hcard
  obtain ⟨d, hd⟩ := card_pos.mp hcount
  exact ⟨hpdata.2, by omega, d, (mem_filter.mp hd).1, (mem_filter.mp hd).2⟩

lemma structuredWitnessPrimes_smooth {r t m p : ℕ} (hrt : r + 2 ≤ t) (hm : 2 ≤ m)
    (hp : p ∈ structuredWitnessPrimes r m (progressionScaleN (t * m))) :
    p.Prime ∧ p ≤ progressionScaleN (t * m) ∧
      p - 1 ∈ Nat.smoothNumbers (2 ^ (64 * (t - r) * m)) := by
  obtain ⟨hprime, hpN, d, hd, hdp⟩ := structuredWitnessPrimes_has_divisor hp
  have hdprops := primeProductModuli_properties hd
  have hdy : d ∈ Nat.smoothNumbers (2 ^ (64 * (t - r) * m)) := by
    apply Nat.smoothNumbers_mono _ (primeProductModuli_smooth hm hd)
    exact Nat.pow_le_pow_right (by decide) (by
      have htr : 2 ≤ t - r := by omega
      nlinarith)
  have hprod : (progressionScaleN m) ^ r * 2 ^ (64 * (t - r) * m) =
      progressionScaleN (t * m) := by
    simp only [progressionScaleN, ← pow_mul, ← pow_add]
    congr 1
    have htr : t - r + r = t := Nat.sub_add_cancel (by omega)
    nlinarith only [congrArg (fun z : ℕ => 64 * z * m) htr]
  have hlarge : p - 1 < d * 2 ^ (64 * (t - r) * m) := by
    calc
      _ < progressionScaleN (t * m) := by have := hprime.two_le; omega
      _ = (progressionScaleN m) ^ r * 2 ^ (64 * (t - r) * m) := hprod.symm
      _ ≤ _ := Nat.mul_le_mul_right _ hdprops.2.2.2.1
  exact ⟨hprime, hpN, smooth_of_large_smooth_divisor
    (Nat.sub_pos_of_lt hprime.one_lt) hdy hdp hlarge⟩

/-- An unconditional structured smooth-prime family in the below-half
modulus range. The smoothness exponent (t-r)/t is still greater than 1/2. -/
theorem eventually_structured_smooth_prime_family (r t : ℕ) (hr : 1 ≤ r)
    (hrt : 2 * r + 1 ≤ t) :
    ∀ᶠ m : ℕ in atTop, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ progressionScaleN (t * m) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ (64 * (t - r) * m)) ∧
        r ≤ (blockPrimeDivisors m (p - 1)).card) ∧
      progressionScaleN (t * m) ≤ structuredPrimeCountConstant r t * (m + 1) ^ (r + 1) * P.card := by
  filter_upwards [eventually_structured_prime_count r t hrt, eventually_ge_atTop 2] with m hcount hm
  refine ⟨structuredWitnessPrimes r m (progressionScaleN (t * m)), ?_, hcount⟩
  intro p hp
  have h := structuredWitnessPrimes_smooth (by omega : r + 2 ≤ t) hm hp
  exact ⟨h.1, h.2.1, h.2.2, (mem_filter.mp hp).2⟩

end Erdos821
