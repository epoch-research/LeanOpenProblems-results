import Submission.ShiftedPrimeCounting

/-!
# A linear Chebyshev lower bound at the progression scales

The earlier lower bound lost a logarithm by assigning every prime the weight
log 2. Discarding the primes below sqrt(N) instead retains a weight comparable
to log N and gives a linear lower bound. No prime number theorem is used.
-/

open scoped BigOperators
open Finset ArithmeticFunction Filter

namespace Erdos821.AnalyticSieve

lemma high_primes_log_le_mangoldt (R N : ℕ) :
    Real.log (R : ℝ) * ((primeModuliBetween R N).card : ℝ) ≤ mangoldtSum N := by
  rw [card_primeModuliBetween]
  let P := (N + 1).primesBelow.filter (fun p => R ≤ p)
  calc
    _ = ∑ p ∈ P, Real.log (R : ℝ) := by simp [P, mul_comm]
    _ ≤ ∑ p ∈ P, vonMangoldt p := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpN, hRp⟩ := mem_filter.mp hp
      rw [vonMangoldt_apply_prime (Nat.mem_primesBelow.mp hpN).2]
      exact log_nat_mono hRp
    _ ≤ mangoldtSum N := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hpN, _⟩ := mem_filter.mp hp
        obtain ⟨hpN, hprime⟩ := Nat.mem_primesBelow.mp hpN
        exact mem_Icc.mpr ⟨hprime.pos, by omega⟩
      · exact fun _ _ _ => vonMangoldt_nonneg

lemma progression_scale_sqrt_ge_linear {s : ℕ} (hs : 1 ≤ s) :
    256 * s ≤ 2 ^ (32 * s) := by
  calc
    256 * s ≤ 2 ^ (31 * s) * 2 ^ s := Nat.mul_le_mul
      (by
        have h := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show 8 ≤ 31 * s by omega)
        norm_num at h ⊢
        exact h) Nat.lt_two_pow_self.le
    _ = 2 ^ (32 * s) := by rw [← pow_add]; congr 1; omega

/-- A genuine linear, not logarithmically weakened, Mangoldt lower bound. -/
theorem progression_scale_mangoldt_lower {s : ℕ} (hs : 1 ≤ s) :
    (progressionScaleN s : ℝ) / 8 ≤ mangoldtSum (progressionScaleN s) := by
  let N := progressionScaleN s
  let R := 2 ^ (32 * s)
  let M := primeModuliBetween R N
  have hR : 1 ≤ R := by dsimp [R]; exact one_le_pow₀ (by norm_num)
  have hRN : R * R = N := by dsimp [R, N, progressionScaleN]; rw [← pow_add]; congr 1; omega
  have hlin : 256 * s ≤ R := progression_scale_sqrt_ge_linear hs
  have hsmall : 128 * s * (R + 1) ≤ N := by nlinarith
  have hcheb : N ≤ (64 * s) * ((N + 1).primesBelow.card + 1) :=
    dyadic_prime_count_bound (64 * s) (by omega)
  have hcard : (N + 1).primesBelow.card ≤ M.card + R := primesBelow_card_le_moduli_add R N
  have hhigh : N ≤ 128 * s * M.card := by nlinarith
  have hlog : 16 * (s : ℝ) ≤ Real.log (R : ℝ) := by
    have ht : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      exact h
    simp only [R, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_mul]
    norm_num
    nlinarith [Nat.cast_nonneg (α := ℝ) s]
  have hweight := high_primes_log_le_mangoldt R N
  have hweight' : 16 * (s : ℝ) * (M.card : ℝ) ≤ mangoldtSum N :=
    (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg _)).trans hweight
  have hhigh' : (N : ℝ) ≤ 128 * (s : ℝ) * (M.card : ℝ) := by exact_mod_cast hhigh
  change (N : ℝ) / 8 ≤ mangoldtSum N
  linarith

/-- Retaining the reciprocal-modulus main term is useful when a second sieve
estimate is to be subtracted from it. -/
theorem progression_scale_weight_lower_reciprocal {s L : ℕ} (hL : 1 ≤ L) (hLs : L ≤ s)
    (hsmall : 32768000000000000 * (s + 1) ^ 7 ≤ 2 ^ L) :
    (progressionScaleN s : ℝ) / 16 *
      (∑ q ∈ primeModuliBetween (progressionScaleD s L) (progressionScaleQ s L),
        (((q : ℕ).totient : ℝ))⁻¹) ≤
      ∑ q ∈ primeModuliBetween (progressionScaleD s L) (progressionScaleQ s L),
        residueOneMangoldt q (progressionScaleN s) := by
  let S : ℝ := ∑ q ∈ primeModuliBetween (progressionScaleD s L) (progressionScaleQ s L),
    (((q : ℕ).totient : ℝ))⁻¹
  have hs : 1 ≤ s := hL.trans hLs
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hspos : (0 : ℝ) < s := by linarith
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  have hcount : 128 * s ≤ 2 ^ L := by
    have hp := Nat.pow_le_pow_right (show 0 < s + 1 by omega) (show 1 ≤ 7 by norm_num)
    simp only [pow_one] at hp
    omega
  have hS : 1 / (64 * (s : ℝ)) ≤ S := by
    apply le_trans _ (moduli_reciprocal_ge_card _ _ (by unfold progressionScaleQ; positivity))
    apply (div_le_div_iff₀ (by positivity) (by unfold progressionScaleQ; positivity)).mpr
    have hc := progression_scale_moduli_count hL hLs hcount
    have hc' : (progressionScaleQ s L : ℝ) ≤ 64 * (s : ℝ) *
        ((primeModuliBetween (progressionScaleD s L) (progressionScaleQ s L)).card : ℝ) := by
      exact_mod_cast hc
    nlinarith
  have herr := progression_scale_error_small hL hLs hsmall
  have herr' : primeProgressionError (progressionScaleU s) (progressionScaleU s)
      (progressionScaleN s) (progressionScaleQ s L) (progressionScaleD s L) ≤
      (progressionScaleN s : ℝ) / 16 * S := by
    apply herr.trans
    calc
      _ ≤ (progressionScaleN s : ℝ) / 16 * (1 / (64 * (s : ℝ))) := by
        rw [show (progressionScaleN s : ℝ) / 16 * (1 / (64 * (s : ℝ))) =
            (progressionScaleN s : ℝ) / (1024 * (s : ℝ)) by ring]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) (by nlinarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left hS (by positivity)
  have hmain := mul_le_mul_of_nonneg_right (progression_scale_mangoldt_lower hs) hS0
  have hbal := progression_scales_balanced hL hLs
  have htotal := prime_progression_total_lower
    (primeModuliBetween (progressionScaleD s L) (progressionScaleQ s L))
    (progressionScaleD s L) (progressionScaleQ s L)
    (by unfold progressionScaleD; positivity) (by unfold progressionScaleQ; positivity)
    (fun q hq => mem_primeModuliBetween.mp hq) (progressionScaleU s) (progressionScaleU s) (progressionScaleN s)
    (by unfold progressionScaleU; exact one_le_pow₀ (by norm_num))
    (hbal.trans (Nat.mul_le_mul_right _ (Nat.le_succ _))) hbal
  change (progressionScaleN s : ℝ) / 16 * S ≤ _
  change mangoldtSum (progressionScaleN s) * S - _ ≤ _ at htotal
  linarith

end Erdos821.AnalyticSieve
