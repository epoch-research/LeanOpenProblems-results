import Submission.CompositeRoughProgressions
import Submission.StructuredPrimeFactors

/-!
# Subtracting rough incidences before dividing by prime multiplicity

The second-sieve rejection is compared directly with the aggregate progression
weight. The binomial incidence bound is used only for the surviving primes and
proper prime powers, not in the ratio between rejection and main term.
-/

open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators

namespace Erdos821

open AnalyticSieve

set_option maxHeartbeats 2000000

noncomputable def smoothStructuredPrimes (r m N Y : ℕ) : Finset ℕ :=
  (structuredWitnessPrimes r m N).filter (fun p => p - 1 ∈ Nat.smoothNumbers Y)

lemma sum_rough_product_counts_eq_incidence (r m N Y : ℕ) :
    (∑ d ∈ primeProductModuli r m, ((roughProgressionPrimes d Y N).card : ℝ)) =
      ∑ n ∈ Icc 1 N,
        if n.Prime ∧ n - 1 ∉ Nat.smoothNumbers Y then
          (((primeProductModuli r m).filter (fun d => d ∣ n - 1)).card : ℝ)
        else 0 := by
  have hset (d : ℕ) : roughProgressionPrimes d Y N =
      (Icc 1 N).filter (fun n => n.Prime ∧ n - 1 ∉ Nat.smoothNumbers Y ∧ d ∣ n - 1) := by
    ext n
    simp only [roughProgressionPrimes, mem_filter, Nat.mem_primesBelow, mem_Icc]
    constructor
    · rintro ⟨⟨hnN, hp⟩, hd, hs⟩
      exact ⟨⟨hp.pos, by omega⟩, hp, hs, hd⟩
    · rintro ⟨⟨hn, hnN⟩, hp, hs, hd⟩
      exact ⟨⟨by omega, hp⟩, hd, hs⟩
  simp only [hset, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  by_cases h : n.Prime ∧ n - 1 ∉ Nat.smoothNumbers Y
  · simp only [h.1, h.2, true_and, not_false_eq_true, if_true]
  · have h' : ∀ d, ¬(n.Prime ∧ n - 1 ∉ Nat.smoothNumbers Y ∧ d ∣ n - 1) :=
      fun _ hd => h ⟨hd.1, hd.2.1⟩
    simp only [if_neg h, if_neg (h' _), sum_const_zero]

/-- The bad incidence count is not multiplied by the prime overcount. -/
theorem product_progression_weight_le_smooth_structured_count (r t m Y : ℕ) (hm : 1 ≤ m) :
    (∑ d ∈ primeProductModuli r m, residueOneMangoldt d (2 ^ (64 * t * m))) ≤
      Real.log (2 ^ (64 * t * m) : ℕ) *
        ((((t - 1).choose r : ℕ) : ℝ) *
          ((smoothStructuredPrimes r m (2 ^ (64 * t * m)) Y).card : ℝ) +
        (∑ d ∈ primeProductModuli r m, ((roughProgressionPrimes d Y (2 ^ (64 * t * m))).card : ℝ)) +
        2 * (((t - 1).choose r : ℕ) : ℝ) * Real.sqrt (2 ^ (64 * t * m) : ℕ)) := by
  let N := 2 ^ (64 * t * m)
  let C : ℝ := ((t - 1).choose r : ℕ)
  let G := smoothStructuredPrimes r m N Y
  let I (n : ℕ) : ℕ := ((primeProductModuli r m).filter (fun d => d ∣ n - 1)).card
  have hN : 1 ≤ N := Nat.one_le_of_lt (by dsimp [N]; positivity)
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg _
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      (I n : ℝ) * vonMangoldt n ≤
        (if n ∈ G then C * Real.log N else 0) +
        (if n.Prime ∧ n - 1 ∉ Nat.smoothNumbers Y then (I n : ℝ) * Real.log N else 0) +
        (if ¬n.Prime then C * vonMangoldt n else 0) := by
    have hnN := (mem_Icc.mp hn).2
    by_cases hn1 : n = 1
    · subst n
      simp only [vonMangoldt_apply_one, mul_zero, ite_self, add_zero, Nat.not_prime_one,
        false_and, if_false]
      split_ifs <;> first | exact mul_nonneg hC hlog | exact le_rfl
    have hn2 : 2 ≤ n := by have := (mem_Icc.mp hn).1; omega
    have hinc : (I n : ℝ) ≤ C := by
      dsimp only [I, C]
      exact_mod_cast prime_product_divisor_count_le_choose r t m (n - 1) hm (by omega)
        (by dsimp [N] at hnN; omega)
    have hwt := mul_le_mul_of_nonneg_right hinc (vonMangoldt_nonneg (n := n))
    by_cases hp : n.Prime
    · rw [if_neg (not_not.mpr hp), add_zero]
      by_cases hs : n - 1 ∈ Nat.smoothNumbers Y
      · rw [if_neg (by tauto : ¬(n.Prime ∧ n - 1 ∉ Nat.smoothNumbers Y)), add_zero]
        by_cases hnG : n ∈ G
        · rw [if_pos hnG]
          exact hwt.trans (mul_le_mul_of_nonneg_left
            (vonMangoldt_le_log.trans (log_nat_mono hnN)) hC)
        · have hlt : (blockPrimeDivisors m (n - 1)).card < r := by
            by_contra h
            apply hnG
            change n ∈ (structuredWitnessPrimes r m N).filter (fun p => p - 1 ∈ Nat.smoothNumbers Y)
            refine mem_filter.mpr ⟨?_, hs⟩
            exact mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega, hp⟩, by omega⟩
          have hzero : I n = 0 := by
            dsimp [I]
            rw [prime_product_divisor_count_eq_choose]
            exact Nat.choose_eq_zero_of_lt hlt
          simp only [if_neg hnG, hzero, Nat.cast_zero, zero_mul, le_refl]
      · have hbad : n.Prime ∧ n - 1 ∉ Nat.smoothNumbers Y := ⟨hp, hs⟩
        rw [if_pos hbad]
        have hwt' : (I n : ℝ) * vonMangoldt n ≤ (I n : ℝ) * Real.log N :=
          mul_le_mul_of_nonneg_left (vonMangoldt_le_log.trans (log_nat_mono hnN)) (Nat.cast_nonneg _)
        split_ifs <;> linarith [mul_nonneg hC hlog]
    · rw [if_pos hp, if_neg (by tauto : ¬(n.Prime ∧ n - 1 ∉ Nat.smoothNumbers Y))]
      split_ifs <;> linarith [mul_nonneg hC hlog]
  have hG : (Icc 1 N).filter (fun n => n ∈ G) = G := by
    ext n
    simp only [mem_filter]
    constructor
    · exact fun h => h.2
    · intro hn
      have hp := (Nat.mem_primesBelow.mp (mem_filter.mp (mem_filter.mp hn).1).1)
      exact ⟨mem_Icc.mpr ⟨hp.2.pos, by omega⟩, hn⟩
  have hrough : (∑ n ∈ Icc 1 N,
      if n.Prime ∧ n - 1 ∉ Nat.smoothNumbers Y then (I n : ℝ) * Real.log N else 0) =
      (∑ d ∈ primeProductModuli r m, ((roughProgressionPrimes d Y N).card : ℝ)) * Real.log N := by
    rw [sum_rough_product_counts_eq_incidence, sum_mul]
    apply sum_congr rfl
    intro n hn
    split_ifs <;> simp only [I, zero_mul]
  calc
    _ = ∑ n ∈ Icc 1 N, (I n : ℝ) * vonMangoldt n := sum_product_progressions_eq_incidence r m N
    _ ≤ ∑ n ∈ Icc 1 N,
        ((if n ∈ G then C * Real.log N else 0) +
          (if n.Prime ∧ n - 1 ∉ Nat.smoothNumbers Y then (I n : ℝ) * Real.log N else 0) +
          (if ¬n.Prime then C * vonMangoldt n else 0)) := sum_le_sum hpoint
    _ = (G.card : ℝ) * (C * Real.log N) +
        (∑ d ∈ primeProductModuli r m, ((roughProgressionPrimes d Y N).card : ℝ)) * Real.log N +
        C * ∑ n ∈ (Icc 1 N).filter (fun n => ¬n.Prime), vonMangoldt n := by
      rw [sum_add_distrib, sum_add_distrib, hrough]
      simp only [← sum_filter, hG, sum_const, nsmul_eq_mul, ← mul_sum]
    _ ≤ (G.card : ℝ) * (C * Real.log N) +
        (∑ d ∈ primeProductModuli r m, ((roughProgressionPrimes d Y N).card : ℝ)) * Real.log N +
        C * (2 * Real.sqrt N * Real.log N) :=
      _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left (mangoldt_nonprime_sum_le N hN) hC)
    _ = _ := by dsimp only [G, C, N]; ring

/-- The unconditional progression lower bound, retaining its reciprocal
modulus weight rather than substituting a weaker numerical lower bound. -/
theorem eventually_product_mangoldt_weight_lower_reciprocal (r t : ℕ)
    (hrt : 2 * r + 1 ≤ t) :
    ∀ᶠ m : ℕ in atTop,
      (progressionScaleN (t * m) : ℝ) / 16 * primeProductReciprocalMass r m ≤
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
  have hW : 0 ≤ primeProductReciprocalMass r m := (by positivity : 0 ≤ 1 / (C * z^r)).trans hmass
  have htm : 1 ≤ t * m := Nat.mul_pos (by omega) (by omega)
  have hpsi : (N : ℝ) / 8 ≤ mangoldtSum N := progression_scale_mangoldt_lower htm
  have hmain := mul_le_mul_of_nonneg_right hpsi hW
  have hbudget : 16 * C ≤ z := by
    have hm' : 16 * primeProductMassConstant r ≤ m + 1 := by omega
    dsimp only [C, z]
    exact_mod_cast hm'
  have herr : (N : ℝ) / z ^ (r + 1) ≤ (N : ℝ) / 16 * primeProductReciprocalMass r m := by
    calc
      _ ≤ (N : ℝ) / (16 * C * z ^ r) := by
        apply div_le_div_of_nonneg_left hN (by positivity)
        rw [pow_succ]
        have h := mul_le_mul_of_nonneg_right hbudget (pow_nonneg hz.le r)
        nlinarith only [h]
      _ = (N : ℝ) / 16 * (1 / (C * z ^ r)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (div_nonneg hN (by norm_num))
  change mangoldtSum N * primeProductReciprocalMass r m - (N : ℝ) / z ^ (r + 1) ≤ _ at htotal
  change (N : ℝ) / 16 * primeProductReciprocalMass r m ≤ _
  linarith only [hmain, herr, htotal]

/-- A finite retention criterion with no incidence factor in the rejection
main-term budget. The analytic hypotheses remain explicit. -/
theorem smooth_structured_weight_retained (r t m Y : ℕ) (hm : 1 ≤ m)
    (A E : ℝ)
    (hweight : (2 ^ (64 * t * m) : ℝ) / 16 * primeProductReciprocalMass r m ≤
      ∑ d ∈ primeProductModuli r m, residueOneMangoldt d (2 ^ (64 * t * m)))
    (hrough : (∑ d ∈ primeProductModuli r m,
      ((roughProgressionPrimes d Y (2 ^ (64 * t * m))).card : ℝ)) ≤
        A * primeProductReciprocalMass r m + E)
    (hmain : Real.log (2 ^ (64 * t * m) : ℕ) * A ≤ (2 ^ (64 * t * m) : ℝ) / 64)
    (herror : Real.log (2 ^ (64 * t * m) : ℕ) *
      (E + 2 * (((t - 1).choose r : ℕ) : ℝ) * Real.sqrt (2 ^ (64 * t * m) : ℕ)) ≤
        (2 ^ (64 * t * m) : ℝ) / 64 * primeProductReciprocalMass r m) :
    (2 ^ (64 * t * m) : ℝ) / 32 * primeProductReciprocalMass r m ≤
      (((t - 1).choose r : ℕ) : ℝ) * Real.log (2 ^ (64 * t * m) : ℕ) *
        ((smoothStructuredPrimes r m (2 ^ (64 * t * m)) Y).card : ℝ) := by
  have hW : 0 ≤ primeProductReciprocalMass r m :=
    sum_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  have hup := product_progression_weight_le_smooth_structured_count r t m Y hm
  have hr := mul_le_mul_of_nonneg_left hrough (Real.log_natCast_nonneg (2 ^ (64 * t * m)))
  have hma := mul_le_mul_of_nonneg_right hmain hW
  linarith only [hweight, hup, hr, hma, herror]

end Erdos821
