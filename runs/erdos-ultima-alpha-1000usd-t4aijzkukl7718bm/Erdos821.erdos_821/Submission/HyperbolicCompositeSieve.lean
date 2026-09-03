import Submission.HyperbolicPrimePairBound
import Submission.BinomialCompositeGain

/-!
# Propagation of the hyperbolic pair bound through composite moduli

The modulus-distribution hypotheses are unchanged. Only the rejected-prime
upper bound is sharpened.
-/

open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

def HyperbolicPairAt (J : ℕ) : Prop :=
  ∀ X a : ℕ, 0 < a → a ≤ X →
    (primePairCofactorCount X a : ℝ) ≤
      ((X : ℝ) / (225*((J : ℝ)*Real.log 2)^2)) *
        (((2*(a : ℝ))/Nat.totient (2*a))^2/(a : ℝ)) +
          ((2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1)

lemma eventually_hyperbolic_pair_at : ∀ᶠ J : ℕ in atTop, HyperbolicPairAt J := by
  filter_upwards [Sieve.eventually_prime_pair_explicit_gain_nine_hundred, eventually_ge_atTop 1]
    with J hpair hJ
  intro X a ha haX
  let D : ℝ := ((J : ℝ)*Real.log 2)^2
  let E : ℝ := (2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1
  have hD : 0 < D := sq_pos_of_pos (mul_pos (by exact_mod_cast hJ)
    (Real.log_pos (by norm_num)))
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hN : ((X/a+1 : ℕ) : ℝ) ≤ 2*(X : ℝ)/a := by
    calc
      _ = ((X/a : ℕ) : ℝ)+1 := by push_cast; rfl
      _ ≤ (X : ℝ)/a+1 := add_le_add Nat.cast_div_le le_rfl
      _ ≤ (X : ℝ)/a+(X : ℝ)/a :=
        add_le_add le_rfl ((one_le_div haR).mpr (by exact_mod_cast haX))
      _ = _ := by ring
  have hb := hpair (X/a+1) a ha
  have heq : 2*((X/a+1 : ℕ) : ℝ)/(900*(((Nat.totient (2*a) : ℝ)/(2*a)*J*Real.log 2)^2)) =
      ((X/a+1 : ℕ) : ℝ)/450 * (((2*(a : ℝ))/Nat.totient (2*a))^2)/D := by
    dsimp [D]
    simp only [mul_pow, div_eq_mul_inv, mul_inv, inv_pow, inv_inv]
    ring
  rw [heq] at hb
  have hE : (2 : ℝ)^(64*J)+1 ≤ E := by
    have hpow : 0 ≤ (2 : ℝ)^(16*J) := by positivity
    dsimp [E]
    linarith
  calc
    _ ≤ ((X/a+1 : ℕ) : ℝ)/450 * (((2*(a : ℝ))/Nat.totient (2*a))^2)/D+E := by
      change (primePairCofactorCount X a : ℝ) ≤ _ at hb
      linarith only [hb, hE]
    _ ≤ (2*(X : ℝ)/a)/450 * (((2*(a : ℝ))/Nat.totient (2*a))^2)/D+E := by gcongr
    _ = _ := by dsimp [D,E]; ring

lemma sum_prime_pair_composite_cofactor_hyperbolic (X K J d : ℕ) (hd : 0 < d)
    (hKX : d * K ≤ X) (hJ : 0 < J) (hsharp : HyperbolicPairAt J) :
    (∑ k ∈ Finset.Icc 1 K, (primePairCofactorCount X (d * k) : ℝ)) ≤
      ((4/225 : ℝ) * Erdos821.Sieve.totientRatioAverageConstant * (X : ℝ) * (harmonic K : ℝ) /
        ((J : ℝ) * Real.log 2) ^ 2) * ((d : ℝ) / (d.totient : ℝ) ^ 2) +
      (K : ℝ) * ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) := by
  let D : ℝ := ((J : ℝ) * Real.log 2) ^ 2
  let E : ℝ := (2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1
  have hD : 0 < D := sq_pos_of_pos (mul_pos (by exact_mod_cast hJ) (Real.log_pos (by norm_num)))
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hb (k : ℕ) (hk : k ∈ Finset.Icc 1 K) :
      (primePairCofactorCount X (d * k) : ℝ) ≤
        ((1/225 : ℝ) * (X : ℝ) * d / (D * (d.totient : ℝ)^2)) *
          (((2 * (k : ℝ)) / Nat.totient (2 * k)) ^ 2 / (k : ℝ)) + E := by
    have hk0 : 0 < k := (mem_Icc.mp hk).1
    have hkX : d * k ≤ X := (Nat.mul_le_mul_left d (mem_Icc.mp hk).2).trans hKX
    have hp := hsharp X (d * k) (Nat.mul_pos hd hk0) hkX
    have hp' : (primePairCofactorCount X (d*k) : ℝ) ≤
        ((1/225 : ℝ)*(X : ℝ)/D)*
          (((2*((d*k : ℕ) : ℝ))/Nat.totient (2*(d*k)))^2/((d*k : ℕ) : ℝ))+E := by
      convert hp using 1
      dsimp [D,E]
      ring
    apply hp'.trans
    calc
      _ ≤ ((1/225 : ℝ) * (X : ℝ) / D) *
          ((((d : ℝ) / d.totient)^2 * ((2 * (k : ℝ)) / Nat.totient (2 * k)) ^ 2) /
            ((d * k : ℕ) : ℝ)) + E := by
        gcongr
        exact composite_cofactor_totient_ratio_sq hd hk0
      _ = _ := by
        push_cast
        field_simp
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 K, (((1/225 : ℝ) * (X : ℝ) * d / (D * (d.totient : ℝ)^2)) *
        (((2 * (k : ℝ)) / Nat.totient (2 * k)) ^ 2 / (k : ℝ)) + E) := sum_le_sum hb
    _ = ((1/225 : ℝ) * (X : ℝ) * d / (D * (d.totient : ℝ)^2)) *
        (∑ k ∈ Finset.Icc 1 K, ((2 * (k : ℝ)) / Nat.totient (2 * k)) ^ 2 / (k : ℝ)) + (K : ℝ) * E := by
      rw [sum_add_distrib, ← Finset.mul_sum]
      simp only [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
    _ ≤ ((1/225 : ℝ) * (X : ℝ) * d / (D * (d.totient : ℝ)^2)) *
        (4 * Erdos821.Sieve.totientRatioAverageConstant * (harmonic K : ℝ)) + (K : ℝ) * E :=
      _root_.add_le_add (mul_le_mul_of_nonneg_left
        (Erdos821.Sieve.totient_ratio_two_mul_harmonic_average K) (by positivity)) le_rfl
    _ = _ := by dsimp [D, E]; ring

lemma rough_composite_progression_prime_count_hyperbolic (X K Y J d : ℕ) (hd : 0 < d)
    (hdY : d ∈ Nat.smoothNumbers Y) (hX : X ≤ d * K * Y)
    (hKX : d * K ≤ X) (hJ : 0 < J) (hsharp : HyperbolicPairAt J) :
    ((roughProgressionPrimes d Y X).card : ℝ) ≤
      ((4/225 : ℝ) * Erdos821.Sieve.totientRatioAverageConstant * (X : ℝ) * (harmonic K : ℝ) /
        ((J : ℝ) * Real.log 2) ^ 2) * ((d : ℝ) / (d.totient : ℝ) ^ 2) +
      (K : ℝ) * ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) := by
  have hc : ((roughProgressionPrimes d Y X).card : ℝ) ≤
      ∑ k ∈ Finset.Icc 1 K, (primePairCofactorCount X (d * k) : ℝ) := by
    exact_mod_cast rough_composite_progression_card_le_pairs X K Y d hd hdY hX
  exact hc.trans (sum_prime_pair_composite_cofactor_hyperbolic X K J d hd hKX hJ hsharp)

/-- A uniform bound close to one on the modulus/totient ratio preserves the
reciprocal-totient progression weight. -/
lemma rough_composite_progression_reciprocal_count_hyperbolic (X K Y J d : ℕ) (hd : 0 < d)
    (hdY : d ∈ Nat.smoothNumbers Y) (hX : X ≤ d * K * Y)
    (hKX : d * K ≤ X) (hJ : 0 < J) (hsharp : HyperbolicPairAt J) (hφd : d ≤ 2 * d.totient) :
    ((roughProgressionPrimes d Y X).card : ℝ) ≤
      ((8/225 : ℝ) * Erdos821.Sieve.totientRatioAverageConstant * (X : ℝ) * (harmonic K : ℝ) /
        ((J : ℝ) * Real.log 2) ^ 2) * (d.totient : ℝ)⁻¹ +
      (K : ℝ) * ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) := by
  apply (rough_composite_progression_prime_count_hyperbolic X K Y J d hd hdY hX hKX hJ hsharp).trans
  have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hφdR : (d : ℝ) ≤ 2 * d.totient := by exact_mod_cast hφd
  have hratio : (d : ℝ) / (d.totient : ℝ)^2 ≤ 2 * (d.totient : ℝ)⁻¹ := by
    apply (div_le_iff₀ (sq_pos_of_pos hφ)).mpr
    convert hφdR using 1
    field_simp
  have hH : 0 ≤ (harmonic K : ℝ) := harmonic_real_nonneg K
  have hC : 0 ≤ Erdos821.Sieve.totientRatioAverageConstant := by
    unfold Erdos821.Sieve.totientRatioAverageConstant
    positivity
  have hnonneg : 0 ≤ (4/225 : ℝ) * Erdos821.Sieve.totientRatioAverageConstant *
      (X : ℝ) * (harmonic K : ℝ) / ((J : ℝ) * Real.log 2)^2 := by positivity
  have h := mul_le_mul_of_nonneg_left hratio hnonneg
  calc
    _ ≤ ((4/225 : ℝ) * Erdos821.Sieve.totientRatioAverageConstant * (X : ℝ) * (harmonic K : ℝ) /
        ((J : ℝ) * Real.log 2) ^ 2) * (2 * (d.totient : ℝ)⁻¹) +
        (K : ℝ) * ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) :=
      _root_.add_le_add h le_rfl
    _ = _ := by ring

/-- This bounds the rejected incidence sum, before any division by a
prime-incidence overcount. -/
theorem rough_composite_family_reciprocal_count_hyperbolic (M : Finset ℕ) (D Q X K Y J : ℕ)
    (hM : ∀ d ∈ M, 0 < d ∧ D ≤ d ∧ d ≤ Q ∧
      d ∈ Nat.smoothNumbers Y ∧ d ≤ 2 * d.totient)
    (hX : X ≤ D * K * Y) (hKX : Q * K ≤ X) (hJ : 0 < J) (hsharp : HyperbolicPairAt J) :
    (∑ d ∈ M, ((roughProgressionPrimes d Y X).card : ℝ)) ≤
      ((8/225 : ℝ) * Erdos821.Sieve.totientRatioAverageConstant * (X : ℝ) * (harmonic K : ℝ) /
        ((J : ℝ) * Real.log 2) ^ 2) * (∑ d ∈ M, (d.totient : ℝ)⁻¹) +
      (M.card : ℝ) * K * ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) := by
  have hb (d : ℕ) (hd : d ∈ M) := rough_composite_progression_reciprocal_count_hyperbolic
    X K Y J d (hM d hd).1 (hM d hd).2.2.2.1
    (hX.trans (Nat.mul_le_mul_right Y (Nat.mul_le_mul_right K (hM d hd).2.1)))
    ((Nat.mul_le_mul_right K (hM d hd).2.2.1).trans hKX) hJ hsharp (hM d hd).2.2.2.2
  apply (sum_le_sum hb).trans_eq
  rw [sum_add_distrib, ← mul_sum]
  simp only [sum_const, nsmul_eq_mul]
  ring


end Erdos821.AnalyticSieve
