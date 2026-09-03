import Submission.NormalizerPrefix

/-! A prime-summed first-hit normalizer tail, using the fifth logarithmic
prime moment. No survivor or Jacobsthal estimate is asserted here. -/
namespace Erdos970.FiniteSelberg
open Finset Real

lemma rankin_exponential_le_nine_fortieths (u : ℝ) :
    exp (9 / 2 - 2 * u) ≤ (9 / 40 : ℝ) * exp (-2 * (u - 3)) := by
  have he : (40 / 9 : ℝ) ≤ exp (3 / 2 : ℝ) := by
    have hh := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) 6
    norm_num [sum_range_succ] at hh
    linarith
  have hinv : exp (-(3 / 2 : ℝ)) ≤ 9 / 40 := by
    rw [exp_neg, ← one_div]
    convert one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 40 / 9) he using 1 <;> norm_num
  rw [show 9 / 2 - 2 * u = -(3 / 2 : ℝ) + -2 * (u - 3) by ring, exp_add]
  exact mul_le_mul_of_nonneg_right hinv (exp_pos _).le

lemma reciprocal_excess_of_sharp_tail (E G r : ℝ) (hE : 0 < E)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ht : E - G ≤ 9 * E * r / 40) :
    0 < G ∧ 1 / G - 1 / E ≤ 9 * r / (31 * E) := by
  have hEr := mul_le_mul_of_nonneg_left hr1 hE.le
  have hGlo : 31 * E / 40 ≤ G := by linarith
  have hG : 0 < G := by linarith
  refine ⟨hG, ?_⟩
  have h1 := mul_le_mul_of_nonneg_left ht (show (0 : ℝ) ≤ 31 by norm_num)
  have h2 := mul_le_mul_of_nonneg_left hGlo (show 0 ≤ 9 * r by positivity)
  apply (sub_le_iff_le_add).mpr
  apply (div_le_iff₀ hG).mpr
  apply (mul_le_mul_iff_right₀ (show 0 < 31 * E by positivity)).mp
  field_simp
  nlinarith only [h1, h2]

lemma strict_normalizer_reciprocal_sharp_tail (p N : ℕ) (hp : p.Prime) (hN : 0 < N)
    (hL : 50 * WeightedMertens.sharpMomentError ≤ log (p : ℝ))
    (hL' : supportMassLogThreshold ≤ log (p : ℝ))
    (u : ℝ) (hu : 3 ≤ u) (hlog : log (N : ℝ) = u * log (p : ℝ)) :
    0 < primeNormalizer p.primesBelow N ∧
    1 / primeNormalizer p.primesBelow N - 1 / eulerMass p.primesBelow ≤
      6 * exp (-2 * (u - 3)) / (31 * log (p : ℝ)) := by
  have he := eulerMass_pos (p + 1).primesBelow
    (fun q hq => (WeightedMertens.mem_primes.mp hq).1)
  have ht := (initial_normalizer_rankin_tail p N hN hL u hlog).trans
    (mul_le_mul_of_nonneg_left (rankin_exponential_le_nine_fortieths u) he.le)
  have ht' := normalizer_strict_prefix_tail (N := N) hp
    ((9 / 40 : ℝ) * exp (-2 * (u - 3))) ht
  obtain ⟨hG, hrec⟩ := reciprocal_excess_of_sharp_tail (eulerMass p.primesBelow)
    (primeNormalizer p.primesBelow N) (exp (-2 * (u - 3)))
    (eulerMass_pos _ (fun q hq => (Nat.mem_primesBelow.mp hq).2))
    (exp_pos _).le (by rw [exp_le_one_iff]; linarith) (by convert ht' using 1 <;> ring)
  refine ⟨hG, hrec.trans ?_⟩
  have hLp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
  have hh := div_le_div_of_nonneg_left (show 0 ≤ 9 * exp (-2 * (u - 3)) by positivity)
    (show 0 < 31 * ((3 / 2 : ℝ) * log (p : ℝ)) by positivity)
    (mul_le_mul_of_nonneg_left (eulerMass_strict_prefix_ge_three_halves p hp hL')
      (by norm_num : (0 : ℝ) ≤ 31))
  convert hh using 1 <;> ring

lemma rankin_tail_le_sixth_power (u : ℝ) (hu : 3 ≤ u) :
    exp (-2 * (u - 3)) ≤ (3 / u) ^ 6 := by
  have hu0 : 0 < u := by linarith
  have hh := log_le_sub_one_of_pos (div_pos hu0 (by norm_num : (0 : ℝ) < 3))
  rw [log_div hu0.ne' (by norm_num)] at hh
  rw [← exp_log (show 0 < (3 / u) ^ 6 by positivity), exp_le_exp, log_pow,
    log_div (by norm_num) hu0.ne']
  norm_num only [Nat.cast_ofNat]
  linarith

/-- A single early prime is charged to its fifth logarithmic moment.
The cutoff is allowed to be any integer satisfying the stated log bound. -/
lemma early_normalizer_excess_le (p N : ℕ) (hp : p.Prime) (hN : 0 < N)
    (L : ℝ) (hL : 0 < L) (hpL : 7 * log (p : ℝ) ≤ L)
    (hcut : (L - log (p : ℝ)) / 2 ≤ log (N : ℝ))
    (hthreshold : 50 * WeightedMertens.sharpMomentError ≤ log (p : ℝ))
    (hthreshold' : supportMassLogThreshold ≤ log (p : ℝ)) :
    (1 / (p : ℝ)) *
      (1 / primeNormalizer p.primesBelow N - 1 / eulerMass p.primesBelow) ≤
      (6 * 7 ^ 6 / (31 * L ^ 6)) * (log (p : ℝ) ^ 5 / p) := by
  let u : ℝ := log (N : ℝ) / log (p : ℝ)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hLp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
  have hlog : log (N : ℝ) = u * log (p : ℝ) := by dsimp [u]; field_simp
  have hu : 3 ≤ u := by
    apply (le_div_iff₀ hLp).mpr
    linarith
  have hrec := (strict_normalizer_reciprocal_sharp_tail p N hp hN
    hthreshold hthreshold' u hu hlog).2
  have hexp := rankin_tail_le_sixth_power u hu
  have hu0 : 0 < u := by linarith
  have hratio : 3 / u ≤ 7 * log (p : ℝ) / L := by
    apply (div_le_div_iff₀ hu0 hL).mpr
    rw [hlog] at hcut
    nlinarith only [hcut, hpL]
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 3 / u) hratio 6
  have hb := hexp.trans hpow
  have hh := mul_le_mul_of_nonneg_left
    (hrec.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num))
      (show 0 ≤ 31 * log (p : ℝ) by positivity))) (show 0 ≤ 1 / (p : ℝ) by positivity)
  convert hh using 1
  field_simp
  <;> ring

/-- The fifth logarithmic prime moment sums the entire early-prime tail.
The missing fixed initial wheel must still be handled separately. -/
theorem first_hit_early_sum_bound (R : ℕ) (hR : 0 < R) (L : ℝ) (hL : 0 < L)
    (hRL : 7 * log (R : ℝ) ≤ L) (P : Finset ℕ) (hP : P ⊆ (R + 1).primesBelow)
    (N : ℕ → ℕ) (hN : ∀ p ∈ P, 0 < N p)
    (hcut : ∀ p ∈ P, (L - log (p : ℝ)) / 2 ≤ log (N p : ℝ))
    (hthreshold : ∀ p ∈ P, 50 * WeightedMertens.sharpMomentError ≤ log (p : ℝ))
    (hthreshold' : ∀ p ∈ P, supportMassLogThreshold ≤ log (p : ℝ)) :
    (∑ p ∈ P, (1 / (p : ℝ)) *
      (1 / primeNormalizer p.primesBelow (N p) - 1 / eulerMass p.primesBelow)) ≤
      42 / (155 * L) + 588 * WeightedMertens.sharpMomentError / (31 * L ^ 2) := by
  let C : ℝ := 6 * 7 ^ 6 / (31 * L ^ 6)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs : (∑ p ∈ P, (1 / (p : ℝ)) *
      (1 / primeNormalizer p.primesBelow (N p) - 1 / eulerMass p.primesBelow)) ≤
      C * ∑ p ∈ (R + 1).primesBelow, log (p : ℝ) ^ 5 / p := by
    calc
      _ ≤ ∑ p ∈ P, C * (log (p : ℝ) ^ 5 / p) := by
        apply sum_le_sum
        intro p hp
        obtain ⟨hpp, hpR⟩ := WeightedMertens.mem_primes.mp (hP hp)
        have hh := log_le_log (show (0 : ℝ) < p by exact_mod_cast hpp.pos)
          (show (p : ℝ) ≤ R by exact_mod_cast hpR)
        exact early_normalizer_excess_le p (N p) hpp (hN p hp) L hL
          (by linarith) (hcut p hp) (hthreshold p hp) (hthreshold' p hp)
      _ = C * ∑ p ∈ P, log (p : ℝ) ^ 5 / p := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hP (fun p _ _ =>
          div_nonneg (pow_nonneg (log_natCast_nonneg p) _) (Nat.cast_nonneg p))) hC
  have hm := (abs_le.mp (WeightedMertens.prime_fifth_log_moment R hR)).2
  have hlogR := log_natCast_nonneg R
  have hp5 := pow_le_pow_left₀ hlogR (show log (R : ℝ) ≤ L / 7 by linarith) 5
  have hp4 := pow_le_pow_left₀ hlogR (show log (R : ℝ) ≤ L / 7 by linarith) 4
  have hMp := WeightedMertens.sharpMomentError_pos
  have hmul := mul_le_mul_of_nonneg_left hp4 (show 0 ≤ 2 * WeightedMertens.sharpMomentError by positivity)
  have hm' : (∑ p ∈ (R + 1).primesBelow, log (p : ℝ) ^ 5 / p) ≤
      (L / 7) ^ 5 / 5 + 2 * WeightedMertens.sharpMomentError * (L / 7) ^ 4 := by linarith
  have hh := hs.trans (mul_le_mul_of_nonneg_left hm' hC)
  convert hh using 1
  dsimp [C]
  field_simp
  <;> ring

lemma first_hit_polynomial_tail_margin :
    (0 : ℝ) < 70 / 19 - 2 * (17 / 10) - 42 / 155 := by norm_num

#print axioms first_hit_early_sum_bound
end Erdos970.FiniteSelberg
