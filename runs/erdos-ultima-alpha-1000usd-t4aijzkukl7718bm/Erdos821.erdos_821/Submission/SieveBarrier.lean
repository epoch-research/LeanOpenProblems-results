import Submission.Sieve

/-!
# A limitation of the explicit rough-prime sieve bound

This file concerns the numerical upper bound in `Sieve.lean`, not the true
number of rough shifted primes. At a smoothness cutoff at most the square
root, this bound is no smaller than the prime-count lower certificate used
there, for every choice of sieve level. Consequently direct subtraction of
these two estimates does not prove a positive smooth-prime count in that
range. This is not a disproof of Erdős 821 or a limitation of all sieve methods.
-/

open Nat Filter

namespace Erdos821.Sieve

noncomputable def dyadicRoughSieveBound (E a J : ℕ) : ℝ :=
  16 * totientRatioAverageConstant * (2 : ℝ) ^ E * (harmonic (2 ^ a) : ℝ) /
      ((J : ℝ) * Real.log 2) ^ 2 +
    (2 : ℝ) ^ a * ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1)

/-- This is exactly the specialization of the existing rough-prime bound
to `X=2^E`, `A=2^a`, `Y=2^(E-a)` and sieve parameter `J`. -/
lemma rough_shifted_prime_card_le_dyadicRoughSieveBound (E a J : ℕ)
    (ha : a ≤ E) (hJ : 0 < J) :
    ((((2 ^ E + 1).primesBelow).filter
      (fun p => p - 1 ∉ Nat.smoothNumbers (2 ^ (E - a)))).card : ℝ) ≤
        dyadicRoughSieveBound E a J := by
  have hXY : (2 : ℕ) ^ E ≤ 2 ^ a * 2 ^ (E - a) := by
    rw [← pow_add, Nat.add_sub_of_le ha]
  have hAX : (2 : ℕ) ^ a ≤ 2 ^ E := Nat.pow_le_pow_right (by decide) ha
  simpa only [dyadicRoughSieveBound, Nat.cast_pow, Nat.cast_ofNat] using
    rough_shifted_prime_explicit_bound (2 ^ E) (2 ^ a) (2 ^ (E - a)) J
      (by positivity) hXY hAX hJ

lemma one_le_totientRatioAverageConstant : 1 ≤ totientRatioAverageConstant := by
  apply Real.one_le_exp
  positivity

lemma log_two_mul_le_harmonic_two_pow (a : ℕ) :
    (a : ℝ) * Real.log 2 ≤ (harmonic (2 ^ a) : ℝ) := by
  calc
    (a : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ a) := (Real.log_pow _ _).symm
    _ ≤ Real.log ((2 ^ a + 1 : ℕ) : ℝ) := by
      apply Real.log_le_log (by positivity)
      push_cast
      linarith
    _ ≤ _ := log_add_one_le_harmonic _

/-- When `A = 2^a ≥ sqrt(2^E)`, the bound used for rough primes cannot beat
the lower certificate `2^E/E` for `π(2^E)+1`, regardless of `J`. -/
lemma dyadicRoughSieveBound_ge_prime_lower_certificate (E a J : ℕ)
    (hE : 0 < E) (hJ : 0 < J) (ha : E ≤ 2 * a) :
    (2 : ℝ) ^ E / E ≤ dyadicRoughSieveBound E a J := by
  let C := totientRatioAverageConstant
  let H : ℝ := harmonic (2 ^ a)
  let c := Real.log 2
  have hC : 1 ≤ C := one_le_totientRatioAverageConstant
  have hH : 0 < H := by
    dsimp [H]
    exact_mod_cast harmonic_pos (by positivity : (2 : ℕ) ^ a ≠ 0)
  have hHlower : (a : ℝ) * c ≤ H := log_two_mul_le_harmonic_two_pow a
  have hc : 0 < c := Real.log_pos (by norm_num)
  have hc1 : c ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    dsimp [c]
    linarith
  have hER : (0 : ℝ) < E := by exact_mod_cast hE
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hD : 0 < ((J : ℝ) * c) ^ 2 := sq_pos_of_pos (mul_pos hJR hc)
  have hmain : 0 ≤ 16 * C * (2 : ℝ) ^ E * H / ((J : ℝ) * c) ^ 2 := by positivity
  have herr : 0 ≤ (2 : ℝ) ^ a * ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) := by positivity
  change (2 : ℝ) ^ E / E ≤
    16 * C * (2 : ℝ) ^ E * H / ((J : ℝ) * c) ^ 2 + _
  by_cases hJE : J ≤ E
  · have hJER : (J : ℝ) ≤ E := by exact_mod_cast hJE
    have haR : (E : ℝ) ≤ 2 * a := by exact_mod_cast ha
    have hden : ((J : ℝ) * c) ^ 2 ≤ 16 * C * H * E := by
      calc
        ((J : ℝ) * c) ^ 2 ≤ ((E : ℝ) * c) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hJER hc.le) _
        _ = (E : ℝ) ^ 2 * c ^ 2 := mul_pow _ _ _
        _ ≤ (E : ℝ) ^ 2 * c :=
          mul_le_mul_of_nonneg_left (by nlinarith : c ^ 2 ≤ c) (sq_nonneg _)
        _ ≤ (2 * (a : ℝ) * E) * c := by
          apply mul_le_mul_of_nonneg_right _ hc.le
          nlinarith
        _ = 2 * ((a : ℝ) * c) * E := by ring
        _ ≤ 2 * H * E := by gcongr
        _ ≤ 16 * C * H * E := by
          gcongr
          linarith
    have hm : (2 : ℝ) ^ E / E ≤ 16 * C * (2 : ℝ) ^ E * H / ((J : ℝ) * c) ^ 2 := by
      apply (div_le_div_iff₀ hER hD).mpr
      calc
        (2 : ℝ) ^ E * ((J : ℝ) * c) ^ 2 ≤ (2 : ℝ) ^ E * (16 * C * H * E) := by
          gcongr
        _ = _ := by ring
    exact hm.trans (le_add_of_nonneg_right herr)
  · have hpow : (2 : ℝ) ^ E ≤ (2 : ℝ) ^ (64 * J) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hA : (1 : ℝ) ≤ (2 : ℝ) ^ a := one_le_pow₀ (by norm_num)
    have hsmall : (2 : ℝ) ^ E / E ≤ (2 : ℝ) ^ E :=
      div_le_self (by positivity) (by exact_mod_cast hE)
    have herror : (2 : ℝ) ^ E ≤
        (2 : ℝ) ^ a * ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) := by
      calc
        (2 : ℝ) ^ E ≤ (2 : ℝ) ^ (64 * J) := hpow
        _ = 1 * (2 : ℝ) ^ (64 * J) := (one_mul _).symm
        _ ≤ (2 : ℝ) ^ a * (2 : ℝ) ^ (64 * J) := by gcongr
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hp : (0 : ℝ) ≤ 2 ^ (16 * J) := by positivity
          linarith
    exact (hsmall.trans herror).trans (le_add_of_nonneg_left hmain)

/-- Direct subtraction of the two existing certificates is nonpositive
when the dyadic smoothness exponent is at most one half. -/
lemma direct_sieve_certificate_nonpos (E b J : ℕ) (hE : 0 < E)
    (hJ : 0 < J) (hb : 2 * b ≤ E) :
    (2 : ℝ) ^ E / E - dyadicRoughSieveBound E (E - b) J ≤ 0 := by
  apply sub_nonpos.mpr
  apply dyadicRoughSieveBound_ge_prime_lower_certificate E (E - b) J hE hJ
  omega

/-- A sharper parameter obstruction: positivity of this particular lower
certificate requires the cofactor exponent to be less than `1/65536` of the
ambient exponent. This does not bound the actual smooth-prime count. -/
lemma positive_direct_sieve_certificate_requires_small_cofactor (E a J : ℕ)
    (hE : 0 < E) (hJ : 0 < J)
    (hbound : dyadicRoughSieveBound E a J < (2 : ℝ) ^ E / E) :
    65536 * a < E := by
  let X : ℝ := 2 ^ E
  let c := Real.log 2
  let C := totientRatioAverageConstant
  let H : ℝ := harmonic (2 ^ a)
  have hX : 0 < X := by dsimp [X]; positivity
  have hc : 0 < c := Real.log_pos (by norm_num)
  have hc1 : c ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    dsimp [c]
    linarith
  have hC : 1 ≤ C := one_le_totientRatioAverageConstant
  have hH : 0 < H := by
    dsimp [H]
    exact_mod_cast harmonic_pos (by positivity : (2 : ℕ) ^ a ≠ 0)
  have hHlower : (a : ℝ) * c ≤ H := log_two_mul_le_harmonic_two_pow a
  have hER : (0 : ℝ) < E := by exact_mod_cast hE
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hD : 0 < ((J : ℝ) * c) ^ 2 := sq_pos_of_pos (mul_pos hJR hc)
  have hmain : 0 ≤ 16 * C * X * H / ((J : ℝ) * c) ^ 2 := by positivity
  have herr : 0 ≤ (2 : ℝ) ^ a * ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) := by positivity
  have herror_lower : (2 : ℝ) ^ (a + 64 * J) ≤ dyadicRoughSieveBound E a J := by
    rw [pow_add]
    apply le_trans ?_ (le_add_of_nonneg_left hmain)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hp : (0 : ℝ) ≤ 2 ^ (16 * J) := by positivity
    linarith
  have hpowlt : (2 : ℝ) ^ (a + 64 * J) < (2 : ℝ) ^ E :=
    (herror_lower.trans_lt hbound).trans_le
      (div_le_self (by positivity) (by exact_mod_cast hE))
  have hexp : a + 64 * J < E := (pow_lt_pow_iff_right₀ (by norm_num : 1 < (2 : ℝ))).mp hpowlt
  have hJE : 64 * (J : ℝ) < E := by exact_mod_cast (show 64 * J < E by omega)
  have hmain_lower : 16 * X * ((a : ℝ) * c) / ((J : ℝ) * c) ^ 2 ≤
      dyadicRoughSieveBound E a J := by
    apply le_trans ?_ (le_add_of_nonneg_right herr)
    apply div_le_div_of_nonneg_right _ hD.le
    calc
      16 * X * ((a : ℝ) * c) = 16 * 1 * X * ((a : ℝ) * c) := by ring
      _ ≤ 16 * C * X * H := by gcongr
  have hmul := (div_lt_div_iff₀ hD hER).mp (hmain_lower.trans_lt hbound)
  have hcancel : X * (c * (16 * (a : ℝ) * E)) < X * (c * ((J : ℝ) ^ 2 * c)) := by
    convert hmul using 1 <;> dsimp [X, c] <;> ring
  have hcofactor : 16 * (a : ℝ) * E < (J : ℝ) ^ 2 := by
    have h := (mul_lt_mul_iff_right₀ hc).mp ((mul_lt_mul_iff_right₀ hX).mp hcancel)
    exact h.trans_le (mul_le_of_le_one_right (sq_nonneg _) hc1)
  have hsq := mul_self_lt_mul_self (by positivity : (0 : ℝ) ≤ 64 * J) hJE
  have hfinal : (65536 : ℝ) * a < E := by
    apply (mul_lt_mul_iff_left₀ hER).mp
    nlinarith
  exact_mod_cast hfinal

#print axioms rough_shifted_prime_card_le_dyadicRoughSieveBound
#print axioms dyadicRoughSieveBound_ge_prime_lower_certificate
#print axioms direct_sieve_certificate_nonpos
#print axioms positive_direct_sieve_certificate_requires_small_cofactor

end Erdos821.Sieve
