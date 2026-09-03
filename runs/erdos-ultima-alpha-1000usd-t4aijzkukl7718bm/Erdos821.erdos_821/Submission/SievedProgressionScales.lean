import Submission.RoughProgressions

/-!
# A second sieve at the concrete progression scales

The surviving primes have predecessors smooth below twice the upper modulus.
For a sufficiently narrow logarithmic modulus interval this lies strictly
below the square-root scale, while the rejected prime-pair contribution is
smaller than the retained main term.
-/

open scoped BigOperators
open Finset ArithmeticFunction Filter

namespace Erdos821.AnalyticSieve

lemma card_primeModuliBetween_le (D Q : ℕ) : (primeModuliBetween D Q).card ≤ Q := by
  rw [card_primeModuliBetween]
  calc
    _ ≤ (Finset.Icc 1 Q).card := by
      apply card_le_card
      intro p hp
      have h := Nat.mem_primesBelow.mp (mem_filter.mp hp).1
      exact mem_Icc.mpr ⟨h.2.pos, by omega⟩
    _ = Q := by simp

lemma progression_scale_reciprocal_lower {s L : ℕ} (hL : 1 ≤ L) (hLs : L ≤ s)
    (hsmall : 128 * s ≤ 2 ^ L) :
    1 / (64 * (s : ℝ)) ≤
      ∑ q ∈ primeModuliBetween (progressionScaleD s L) (progressionScaleQ s L),
        (((q : ℕ).totient : ℝ))⁻¹ := by
  have hs : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  apply le_trans _ (moduli_reciprocal_ge_card _ _ (by unfold progressionScaleQ; positivity))
  apply (div_le_div_iff₀ (by positivity) (by unfold progressionScaleQ; positivity)).mpr
  have hc := progression_scale_moduli_count hL hLs hsmall
  have hc' : (progressionScaleQ s L : ℝ) ≤ 64 * (s : ℝ) *
      ((primeModuliBetween (progressionScaleD s L) (progressionScaleQ s L)).card : ℝ) := by
    exact_mod_cast hc
  nlinarith

def progressionSieveK (L : ℕ) : ℕ := 2 ^ (5 * L)
def progressionSieveY (s L : ℕ) : ℕ := 2 * progressionScaleQ s L

lemma progression_sieve_modulus_factorization {s L : ℕ} (hLs : L ≤ s) :
    progressionScaleD s L * progressionSieveK L * progressionScaleQ s L = progressionScaleN s := by
  simp only [progressionScaleD, progressionSieveK, progressionScaleQ, progressionScaleN, ← pow_add]
  congr 1
  omega

lemma progression_sieve_cofactor_le {s L : ℕ} (hLs : L ≤ s) :
    progressionScaleQ s L * progressionSieveK L ≤ progressionScaleN s := by
  simp only [progressionScaleQ, progressionSieveK, progressionScaleN, ← pow_add]
  exact Nat.pow_le_pow_right (by decide) (by omega)

lemma progression_sieve_harmonic_le {L : ℕ} (hL : 1 ≤ L) :
    (harmonic (progressionSieveK L) : ℝ) ≤ 6 * (L : ℝ) := by
  have h := harmonic_le_one_add_log (progressionSieveK L)
  have hlog := log_two_pow_le (5 * L)
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hlog
  change Real.log (progressionSieveK L) ≤ 5 * (L : ℝ) at hlog
  linarith

lemma progression_sieve_pair_error {s L J : ℕ} (hLs : L ≤ s) (hJ : 4 * J = s) :
    ((primeModuliBetween (progressionScaleD s L) (progressionScaleQ s L)).card : ℝ) *
      progressionSieveK L * ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) ≤
        3 * (progressionScaleB s L : ℝ) := by
  have hc : ((primeModuliBetween (progressionScaleD s L) (progressionScaleQ s L)).card : ℝ) ≤
      progressionScaleQ s L := by exact_mod_cast card_primeModuliBetween_le _ _
  have hp : (2 : ℝ) ^ (16 * J) ≤ (2 : ℝ) ^ (64 * J) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hp1 : (1 : ℝ) ≤ (2 : ℝ) ^ (64 * J) := one_le_pow₀ (by norm_num)
  have he : (2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1 ≤ 3 * (2 : ℝ) ^ (64 * J) := by linarith
  have hpow : (progressionScaleQ s L : ℝ) * progressionSieveK L * (2 : ℝ) ^ (64 * J) ≤
      (progressionScaleB s L : ℝ) := by
    simp only [progressionScaleQ, progressionSieveK, progressionScaleB, Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    _ ≤ (progressionScaleQ s L : ℝ) * progressionSieveK L * (3 * (2 : ℝ) ^ (64 * J)) := by gcongr
    _ = 3 * ((progressionScaleQ s L : ℝ) * progressionSieveK L * (2 : ℝ) ^ (64 * J)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by norm_num)

lemma progression_sieve_rejection_main {s L J : ℕ} (hL : 1 ≤ L) (hLs : L ≤ s) (hJ : 4 * J = s)
    (hC : 201326592 * Erdos821.Sieve.totientRatioAverageConstant * (L : ℝ) ≤ (s : ℝ)) :
    2 * Real.log (progressionScaleN s) *
      (64 * Erdos821.Sieve.totientRatioAverageConstant * (progressionScaleN s : ℝ) *
        (harmonic (progressionSieveK L) : ℝ) / ((J : ℝ) * Real.log 2) ^ 2) ≤
      (progressionScaleN s : ℝ) / 64 := by
  let C := Erdos821.Sieve.totientRatioAverageConstant
  let H : ℝ := harmonic (progressionSieveK L)
  let d : ℝ := ((J : ℝ) * Real.log 2) ^ 2
  have hC0 : 0 ≤ C := by dsimp [C, Erdos821.Sieve.totientRatioAverageConstant]; positivity
  have hH0 : 0 ≤ H := harmonic_real_nonneg _
  have hs : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hJ' : 4 * (J : ℝ) = s := by exact_mod_cast hJ
  have hd : 0 < d := sq_pos_of_pos (mul_pos hJpos (Real.log_pos (by norm_num)))
  have hdlo : (s : ℝ) ^ 2 / 64 ≤ d := by
    have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      exact h
    have hm := mul_le_mul_of_nonneg_left hlog hJpos.le
    have hh : (s : ℝ) / 8 ≤ (J : ℝ) * Real.log 2 := by linarith
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (s : ℝ) / 8) hh 2
    simpa only [div_pow, show (8 : ℝ) ^ 2 = 64 by norm_num] using hp
  have hlogN : Real.log (progressionScaleN s) ≤ 64 * (s : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using log_two_pow_le (64 * s)
  have hnum : 2 * Real.log (progressionScaleN s) * (64 * C * H) ≤ d / 64 := by
    calc
      _ ≤ 2 * (64 * (s : ℝ)) * (64 * C * (6 * (L : ℝ))) := by
        gcongr
        exact progression_sieve_harmonic_le hL
      _ = 49152 * C * (L : ℝ) * s := by ring
      _ ≤ (s : ℝ) ^ 2 / 4096 := by
        have hm := mul_le_mul_of_nonneg_right hC hs.le
        dsimp [C]
        nlinarith
      _ ≤ d / 64 := by linarith
  have hcoeff : 2 * Real.log (progressionScaleN s) * (64 * C * H / d) ≤ 1 / 64 := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hd).mpr (by linarith)
  calc
    _ = (progressionScaleN s : ℝ) * (2 * Real.log (progressionScaleN s) * (64 * C * H / d)) := by
      dsimp [C, H, d]
      ring
    _ ≤ (progressionScaleN s : ℝ) * (1 / 64) := mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg _)
    _ = _ := by ring

noncomputable def sievedProgressionPrimes (s L : ℕ) : Finset ℕ :=
  (shiftedWitnessPrimes
    (primeModuliBetween (progressionScaleD s L) (progressionScaleQ s L))
    (progressionScaleB s L) (progressionScaleN s)).filter
      (fun p => p - 1 ∈ Nat.smoothNumbers (progressionSieveY s L))

/-- After rejecting nonsmooth predecessors, a power-density supply remains.
The constant restriction on L/s is independent of the scale. -/
theorem sieved_progression_prime_reciprocal_count {s L J : ℕ} (hL : 1 ≤ L) (hLs : L ≤ s) (hJ : 4 * J = s)
    (hsmall : 32768000000000000 * (s + 1) ^ 7 ≤ 2 ^ L)
    (hC : 201326592 * Erdos821.Sieve.totientRatioAverageConstant * (L : ℝ) ≤ (s : ℝ)) :
    (progressionScaleN s : ℝ) *
      (∑ q ∈ primeModuliBetween (progressionScaleD s L) (progressionScaleQ s L),
        (((q : ℕ).totient : ℝ))⁻¹) ≤
      4096 * (s : ℝ) * ((sievedProgressionPrimes s L).card : ℝ) := by
  classical
  let N := progressionScaleN s
  let B := progressionScaleB s L
  let Y := progressionSieveY s L
  let K := progressionSieveK L
  let M := primeModuliBetween (progressionScaleD s L) (progressionScaleQ s L)
  let P := shiftedWitnessPrimes M B N
  let G := sievedProgressionPrimes s L
  let R := P.filter (fun p => p - 1 ∉ Nat.smoothNumbers Y)
  let S : ℝ := ∑ q ∈ M, (((q : ℕ).totient : ℝ))⁻¹
  let A : ℝ := 64 * Erdos821.Sieve.totientRatioAverageConstant * (N : ℝ) * (harmonic K : ℝ) /
    ((J : ℝ) * Real.log 2) ^ 2
  have hs : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hN : (0 : ℝ) < N := by dsimp [N, progressionScaleN]; positivity
  have hS0 : 0 ≤ S := sum_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg _
  have hlog : Real.log (N : ℝ) ≤ 64 * (s : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using log_two_pow_le (64 * s)
  have hpoly : 3145728 * s ^ 2 ≤ 2 ^ L := by
    have hp : s ^ 2 ≤ (s + 1) ^ 7 :=
      (Nat.pow_le_pow_left (Nat.le_succ s) 2).trans
        (Nat.pow_le_pow_right (show 0 < s + 1 by omega) (by norm_num : 2 ≤ 7))
    omega
  have hcount : 128 * s ≤ 2 ^ L := by nlinarith [show 1 ≤ s by omega]
  have hS : 1 / (64 * (s : ℝ)) ≤ S := progression_scale_reciprocal_lower hL hLs hcount
  have hBsmall : 768 * (s : ℝ) * (B : ℝ) ≤ (N : ℝ) / 64 * S := by
    calc
      _ ≤ (N : ℝ) / (4096 * (s : ℝ)) := by
        apply (le_div_iff₀ (by positivity)).mpr
        have hp : 3145728 * (s : ℝ) ^ 2 ≤ (2 : ℝ) ^ L := by exact_mod_cast hpoly
        have hm := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α := ℝ) B)
        have heq : (2 : ℝ) ^ L * (B : ℝ) = (N : ℝ) := by
          exact_mod_cast (by rw [mul_comm]; exact progressionScaleB_mul hLs)
        rw [heq] at hm
        nlinarith
      _ = (N : ℝ) / 64 * (1 / (64 * (s : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hS (by positivity)
  have hR : (R.card : ℝ) ≤ A * S + 3 * (B : ℝ) := by
    have hQ : progressionScaleQ s L < Y := by
      dsimp [Y, progressionSieveY]
      have : 0 < progressionScaleQ s L := by unfold progressionScaleQ; positivity
      omega
    have hNKY : N ≤ progressionScaleD s L * K * Y := by
      dsimp [Y, progressionSieveY]
      have heq := progression_sieve_modulus_factorization hLs
      change progressionScaleD s L * K * progressionScaleQ s L = N at heq
      nlinarith
    have hb := rough_witness_prime_count_le M (progressionScaleD s L) (progressionScaleQ s L) B Y N K J
      (fun q hq => mem_primeModuliBetween.mp hq) hQ hNKY (progression_sieve_cofactor_le hLs) (by omega)
    exact hb.trans (add_le_add le_rfl (progression_sieve_pair_error hLs hJ))
  have hGcard : P.card = G.card + R.card := by
    exact (card_filter_add_card_filter_not (s := P) (p := fun p => p - 1 ∈ Nat.smoothNumbers Y)).symm
  have hsqrt : Real.sqrt (N : ℝ) ≤ (B : ℝ) := by
    rw [sqrt_progressionScaleN]
    simp only [B, progressionScaleB, Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hu := progression_weight_le_prime_count M (progressionScaleD s L) B N
    (fun q hq => ⟨(mem_primeModuliBetween.mp hq).1, (mem_primeModuliBetween.mp hq).2.1⟩)
    (by dsimp [N, progressionScaleN]; exact one_le_pow₀ (by norm_num)) (progression_scale_cube hL hLs)
  have hRmain : 2 * Real.log (N : ℝ) * A ≤ (N : ℝ) / 64 := progression_sieve_rejection_main hL hLs hJ hC
  have hupper : (∑ q ∈ M, residueOneMangoldt q N) ≤
      128 * (s : ℝ) * (G.card : ℝ) + (N : ℝ) / 32 * S := by
    calc
      _ ≤ 2 * Real.log (N : ℝ) * ((G.card : ℝ) + (A * S + 3 * (B : ℝ)) + B + 2 * (B : ℝ)) := by
        apply hu.trans
        rw [hGcard, Nat.cast_add]
        gcongr
      _ = 2 * Real.log (N : ℝ) * (G.card : ℝ) +
          (2 * Real.log (N : ℝ) * A) * S + 12 * Real.log (N : ℝ) * (B : ℝ) := by ring
      _ ≤ 128 * (s : ℝ) * (G.card : ℝ) + ((N : ℝ) / 64) * S + 768 * (s : ℝ) * (B : ℝ) := by
        exact add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right (by linarith : 2 * Real.log (N : ℝ) ≤ 128 * (s : ℝ)) (Nat.cast_nonneg _))
          (mul_le_mul_of_nonneg_right hRmain hS0))
          (mul_le_mul_of_nonneg_right (by linarith : 12 * Real.log (N : ℝ) ≤ 768 * (s : ℝ)) (Nat.cast_nonneg _))
      _ ≤ 128 * (s : ℝ) * (G.card : ℝ) + ((N : ℝ) / 64) * S + ((N : ℝ) / 64) * S := by gcongr
      _ = _ := by ring
  have hlower : (N : ℝ) / 16 * S ≤ ∑ q ∈ M, residueOneMangoldt q N :=
    progression_scale_weight_lower_reciprocal hL hLs hsmall
  have hG : (N : ℝ) / 32 * S ≤ 128 * (s : ℝ) * (G.card : ℝ) := by linarith
  change (N : ℝ) * S ≤ 4096 * (s : ℝ) * (G.card : ℝ)
  nlinarith

/-- The coarser power-density form follows from the reciprocal-weighted count. -/
theorem sieved_progression_prime_count {s L J : ℕ} (hL : 1 ≤ L) (hLs : L ≤ s) (hJ : 4 * J = s)
    (hsmall : 32768000000000000 * (s + 1) ^ 7 ≤ 2 ^ L)
    (hC : 201326592 * Erdos821.Sieve.totientRatioAverageConstant * (L : ℝ) ≤ (s : ℝ)) :
    progressionScaleN s ≤ 262144 * s ^ 2 * (sievedProgressionPrimes s L).card := by
  have hs : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hcount : 128 * s ≤ 2 ^ L := by
    have hp := Nat.pow_le_pow_right (show 0 < s + 1 by omega) (show 1 ≤ 7 by norm_num)
    simp only [pow_one] at hp
    omega
  have hS := progression_scale_reciprocal_lower hL hLs hcount
  have hc := sieved_progression_prime_reciprocal_count hL hLs hJ hsmall hC
  have hlow := mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg (α := ℝ) (progressionScaleN s))
  have hh : (progressionScaleN s : ℝ) / (64 * (s : ℝ)) ≤
      4096 * (s : ℝ) * ((sievedProgressionPrimes s L).card : ℝ) := by
    simpa only [mul_one_div] using hlow.trans hc
  have hm := (div_le_iff₀ (by positivity : (0 : ℝ) < 64 * (s : ℝ))).mp hh
  have hfinal : (progressionScaleN s : ℝ) ≤
      262144 * (s : ℝ) ^ 2 * ((sievedProgressionPrimes s L).card : ℝ) := by nlinarith
  exact_mod_cast hfinal

end Erdos821.AnalyticSieve
