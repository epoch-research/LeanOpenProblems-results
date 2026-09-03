import Submission.FirstHitEarlyTail

/-! A sharper far-prime bound beyond logarithmic ratio four, obtained from
an eighth-power tail and the seventh prime logarithmic moment. -/
namespace Erdos970.FiniteSelberg
open Finset Real

lemma rankin_tail_le_eighth_power (u : ℝ) (hu : 4 ≤ u) :
    exp (-2 * (u - 3)) ≤ (1 / 7 : ℝ) * (4 / u) ^ 8 := by
  have hu0 : 0 < u := by linarith
  have hh := log_le_sub_one_of_pos (div_pos hu0 (by norm_num : (0 : ℝ) < 4))
  rw [log_div hu0.ne' (by norm_num)] at hh
  have ht : exp (-2 * (u - 4)) ≤ (4 / u) ^ 8 := by
    rw [← exp_log (show 0 < (4 / u) ^ 8 by positivity), exp_le_exp, log_pow,
      log_div (by norm_num) hu0.ne']
    norm_num only [Nat.cast_ofNat]
    linarith
  have he : (7 : ℝ) ≤ exp 2 := by
    have h := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 5
    norm_num [sum_range_succ] at h
    exact h
  have he' : exp (-2 : ℝ) ≤ 1 / 7 := by
    rw [exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) he
  rw [show -2 * (u - 3) = -2 + -2 * (u - 4) by ring, exp_add]
  exact mul_le_mul he' ht (exp_pos _).le (by norm_num)

/-- A single early prime is charged to its seventh logarithmic moment.
The cutoff is allowed to be any integer satisfying the stated log bound. -/
lemma far_normalizer_excess_le (p N : ℕ) (hp : p.Prime) (hN : 0 < N)
    (L : ℝ) (hL : 0 < L) (hpL : 9 * log (p : ℝ) ≤ L)
    (hcut : (L - log (p : ℝ)) / 2 ≤ log (N : ℝ))
    (hthreshold : 50 * WeightedMertens.sharpMomentError ≤ log (p : ℝ))
    (hthreshold' : supportMassLogThreshold ≤ log (p : ℝ)) :
    (1 / (p : ℝ)) *
      (1 / primeNormalizer p.primesBelow N - 1 / eulerMass p.primesBelow) ≤
      (6 * 9 ^ 8 / (217 * L ^ 8)) * (log (p : ℝ) ^ 7 / p) := by
  let u : ℝ := log (N : ℝ) / log (p : ℝ)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hLp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
  have hlog : log (N : ℝ) = u * log (p : ℝ) := by dsimp [u]; field_simp
  have hu : 4 ≤ u := by
    apply (le_div_iff₀ hLp).mpr
    linarith
  have hrec := (strict_normalizer_reciprocal_sharp_tail p N hp hN
    hthreshold hthreshold' u (by linarith) hlog).2
  have hexp := rankin_tail_le_eighth_power u hu
  have hu0 : 0 < u := by linarith
  have hratio : 4 / u ≤ 9 * log (p : ℝ) / L := by
    apply (div_le_div_iff₀ hu0 hL).mpr
    rw [hlog] at hcut
    nlinarith only [hcut, hpL]
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 4 / u) hratio 8
  have hb := hexp.trans (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 1 / 7))
  have hh := mul_le_mul_of_nonneg_left
    (hrec.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num))
      (show 0 ≤ 31 * log (p : ℝ) by positivity))) (show 0 ≤ 1 / (p : ℝ) by positivity)
  convert hh using 1
  field_simp
  <;> ring

/-- The seventh logarithmic prime moment sums the entire early-prime tail.
The missing fixed initial wheel must still be handled separately. -/
theorem first_hit_far_sum_bound (R : ℕ) (hR : 0 < R) (L : ℝ) (hL : 0 < L)
    (hRL : 9 * log (R : ℝ) ≤ L) (P : Finset ℕ) (hP : P ⊆ (R + 1).primesBelow)
    (N : ℕ → ℕ) (hN : ∀ p ∈ P, 0 < N p)
    (hcut : ∀ p ∈ P, (L - log (p : ℝ)) / 2 ≤ log (N p : ℝ))
    (hthreshold : ∀ p ∈ P, 50 * WeightedMertens.sharpMomentError ≤ log (p : ℝ))
    (hthreshold' : ∀ p ∈ P, supportMassLogThreshold ≤ log (p : ℝ)) :
    (∑ p ∈ P, (1 / (p : ℝ)) *
      (1 / primeNormalizer p.primesBelow (N p) - 1 / eulerMass p.primesBelow)) ≤
      54 / (1519 * L) + 972 * WeightedMertens.sharpMomentError / (217 * L ^ 2) := by
  let C : ℝ := 6 * 9 ^ 8 / (217 * L ^ 8)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs : (∑ p ∈ P, (1 / (p : ℝ)) *
      (1 / primeNormalizer p.primesBelow (N p) - 1 / eulerMass p.primesBelow)) ≤
      C * ∑ p ∈ (R + 1).primesBelow, log (p : ℝ) ^ 7 / p := by
    calc
      _ ≤ ∑ p ∈ P, C * (log (p : ℝ) ^ 7 / p) := by
        apply sum_le_sum
        intro p hp
        obtain ⟨hpp, hpR⟩ := WeightedMertens.mem_primes.mp (hP hp)
        have hh := log_le_log (show (0 : ℝ) < p by exact_mod_cast hpp.pos)
          (show (p : ℝ) ≤ R by exact_mod_cast hpR)
        exact far_normalizer_excess_le p (N p) hpp (hN p hp) L hL
          (by linarith) (hcut p hp) (hthreshold p hp) (hthreshold' p hp)
      _ = C * ∑ p ∈ P, log (p : ℝ) ^ 7 / p := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hP (fun p _ _ =>
          div_nonneg (pow_nonneg (log_natCast_nonneg p) _) (Nat.cast_nonneg p))) hC
  have hm := (abs_le.mp (WeightedMertens.prime_log_moment R hR 5)).2
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hm
  have hlogR := log_natCast_nonneg R
  have hp5 := pow_le_pow_left₀ hlogR (show log (R : ℝ) ≤ L / 9 by linarith) 7
  have hp4 := pow_le_pow_left₀ hlogR (show log (R : ℝ) ≤ L / 9 by linarith) 6
  have hMp := WeightedMertens.sharpMomentError_pos
  have hmul := mul_le_mul_of_nonneg_left hp4 (show 0 ≤ 2 * WeightedMertens.sharpMomentError by positivity)
  have hm' : (∑ p ∈ (R + 1).primesBelow, log (p : ℝ) ^ 7 / p) ≤
      (L / 9) ^ 7 / 7 + 2 * WeightedMertens.sharpMomentError * (L / 9) ^ 6 := by linarith
  have hh := hs.trans (mul_le_mul_of_nonneg_left hm' hC)
  convert hh using 1
  dsimp [C]
  field_simp
  <;> ring


#print axioms first_hit_far_sum_bound
end Erdos970.FiniteSelberg
