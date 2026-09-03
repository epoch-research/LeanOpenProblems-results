import Submission.MixedTotientAverage
import Submission.BinomialCompositeGain

/-!
# The mixed-root sieve for composite progression moduli

The main term now has a single reciprocal totient, and constant 1/75.
-/

open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

def MixedPairAt (J : ℕ) : Prop :=
  ∀ X a : ℕ, 0 < a → a ≤ X →
    (primePairCofactorCount X a : ℝ) ≤
      (X : ℝ)/(225*(a.totient : ℝ)*((J : ℝ)*Real.log 2)^2) +
        ((2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1)

lemma eventually_mixed_pair_at : ∀ᶠ J : ℕ in atTop, MixedPairAt J := by
  filter_upwards [Sieve.eventually_prime_pair_mixed_explicit_all, eventually_ge_atTop 1]
    with J hpair hJ
  intro X a ha haX
  let D : ℝ := ((J : ℝ)*Real.log 2)^2
  let E : ℝ := (2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1
  have hD : 0 < D := sq_pos_of_pos (mul_pos (by exact_mod_cast hJ) (Real.log_pos (by norm_num)))
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hφ : (0 : ℝ) < a.totient := by exact_mod_cast Nat.totient_pos.mpr ha
  have hN : ((X/a+1 : ℕ) : ℝ) ≤ 2*(X : ℝ)/a := by
    calc
      _ = ((X/a : ℕ) : ℝ)+1 := by push_cast; rfl
      _ ≤ (X : ℝ)/a+1 := add_le_add Nat.cast_div_le le_rfl
      _ ≤ (X : ℝ)/a+(X : ℝ)/a :=
        add_le_add le_rfl ((one_le_div haR).mpr (by exact_mod_cast haX))
      _ = _ := by ring
  have hb := hpair (X/a+1) a ha
  have hE : (2 : ℝ)^(64*J)+1 ≤ E := by
    have hpow : 0 ≤ (2 : ℝ)^(16*J) := by positivity
    dsimp [E]
    linarith
  calc
    _ ≤ 2*((X/a+1 : ℕ) : ℝ)/(900*((Nat.totient a : ℝ)/a*D))+E := by
      change (primePairCofactorCount X a : ℝ) ≤ _ at hb
      linarith only [hb, hE]
    _ ≤ 2*(2*(X : ℝ)/a)/(900*((Nat.totient a : ℝ)/a*D))+E := by gcongr
    _ = _ := by dsimp [D,E]; field_simp; ring

lemma sum_prime_pair_composite_cofactor_mixed (X K J d : ℕ) (hd : 0 < d)
    (hKX : d*K ≤ X) (hJ : 0 < J) (hmixed : MixedPairAt J) :
    (∑ k ∈ Icc 1 K, (primePairCofactorCount X (d*k) : ℝ)) ≤
      ((1/75 : ℝ)*(X : ℝ)*(harmonic K : ℝ)/((J : ℝ)*Real.log 2)^2) * (d.totient : ℝ)⁻¹ +
      (K : ℝ)*((2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1) := by
  let D : ℝ := ((J : ℝ)*Real.log 2)^2
  let E : ℝ := (2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1
  have hD : 0 < D := sq_pos_of_pos (mul_pos (by exact_mod_cast hJ) (Real.log_pos (by norm_num)))
  have hφd : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hb (k : ℕ) (hk : k ∈ Icc 1 K) :
      (primePairCofactorCount X (d*k) : ℝ) ≤
        ((X : ℝ)/(225*(d.totient : ℝ)*D))*(1/(k.totient : ℝ))+E := by
    have hk0 : 0 < k := (mem_Icc.mp hk).1
    have hφk : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.mpr hk0
    have hφdk : (d.totient : ℝ)*k.totient ≤ (d*k).totient := by
      exact_mod_cast Nat.totient_super_multiplicative d k
    have hp := hmixed X (d*k) (Nat.mul_pos hd hk0)
      ((Nat.mul_le_mul_left d (mem_Icc.mp hk).2).trans hKX)
    apply hp.trans
    calc
      _ ≤ (X : ℝ)/(225*((d.totient : ℝ)*k.totient)*D)+E := by
        apply _root_.add_le_add _ le_rfl
        apply div_le_div_of_nonneg_left (Nat.cast_nonneg X) (by positivity)
        gcongr
      _ = _ := by ring
  calc
    _ ≤ ∑ k ∈ Icc 1 K, (((X : ℝ)/(225*(d.totient : ℝ)*D))*(1/(k.totient : ℝ))+E) := sum_le_sum hb
    _ = ((X : ℝ)/(225*(d.totient : ℝ)*D))*(∑ k ∈ Icc 1 K, 1/(k.totient : ℝ)) + (K : ℝ)*E := by
      rw [sum_add_distrib, ← Finset.mul_sum]
      simp only [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
    _ ≤ ((X : ℝ)/(225*(d.totient : ℝ)*D))*(3*(harmonic K : ℝ)) + (K : ℝ)*E :=
      _root_.add_le_add (mul_le_mul_of_nonneg_left
        (Sieve.sum_reciprocal_totient_le_three_harmonic K) (by positivity)) le_rfl
    _ = _ := by dsimp [D,E]; ring

lemma rough_composite_progression_reciprocal_count_mixed (X K Y J d : ℕ) (hd : 0 < d)
    (hdY : d ∈ Nat.smoothNumbers Y) (hX : X ≤ d*K*Y)
    (hKX : d*K ≤ X) (hJ : 0 < J) (hmixed : MixedPairAt J) :
    ((roughProgressionPrimes d Y X).card : ℝ) ≤
      ((1/75 : ℝ)*(X : ℝ)*(harmonic K : ℝ)/((J : ℝ)*Real.log 2)^2) * (d.totient : ℝ)⁻¹ +
      (K : ℝ)*((2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1) := by
  have hc : ((roughProgressionPrimes d Y X).card : ℝ) ≤
      ∑ k ∈ Icc 1 K, (primePairCofactorCount X (d*k) : ℝ) := by
    exact_mod_cast rough_composite_progression_card_le_pairs X K Y d hd hdY hX
  exact hc.trans (sum_prime_pair_composite_cofactor_mixed X K J d hd hKX hJ hmixed)

/-- Unlike the old bound, this does not assume d ≤ 2φ(d). -/
theorem rough_composite_family_reciprocal_count_mixed (M : Finset ℕ) (D Q X K Y J : ℕ)
    (hM : ∀ d ∈ M, 0 < d ∧ D ≤ d ∧ d ≤ Q ∧ d ∈ Nat.smoothNumbers Y)
    (hX : X ≤ D*K*Y) (hKX : Q*K ≤ X) (hJ : 0 < J) (hmixed : MixedPairAt J) :
    (∑ d ∈ M, ((roughProgressionPrimes d Y X).card : ℝ)) ≤
      ((1/75 : ℝ)*(X : ℝ)*(harmonic K : ℝ)/((J : ℝ)*Real.log 2)^2) * (∑ d ∈ M, (d.totient : ℝ)⁻¹) +
      (M.card : ℝ)*K*((2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1) := by
  have hb (d : ℕ) (hd : d ∈ M) := rough_composite_progression_reciprocal_count_mixed
    X K Y J d (hM d hd).1 (hM d hd).2.2.2
    (hX.trans (Nat.mul_le_mul_right Y (Nat.mul_le_mul_right K (hM d hd).2.1)))
    ((Nat.mul_le_mul_right K (hM d hd).2.2.1).trans hKX) hJ hmixed
  apply (sum_le_sum hb).trans_eq
  rw [sum_add_distrib, ← mul_sum]
  simp only [sum_const, nsmul_eq_mul]
  ring

end Erdos821.AnalyticSieve
