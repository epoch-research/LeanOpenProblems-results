import Submission.EndpointPrimePairBound

/-!
# The composite-modulus sieve without the multiplicative endpoint loss
-/

open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

lemma sum_prime_pair_composite_cofactor_endpoint (X K J d : ℕ) (hd : 0 < d) (hdodd : Odd d)
    (hKX : d*K ≤ X) (hKcap : d*K ≤ 2^(256*J)) (hJ : 0 < J) (hmixed : EndpointPairAt J) :
    (∑ k ∈ Icc 1 K, (primePairCofactorCount X (d*k) : ℝ)) ≤
      ((2/675 : ℝ)*(X : ℝ)*(harmonic K : ℝ)/((J : ℝ)*Real.log 2)^2) * (d.totient : ℝ)⁻¹ +
      (K : ℝ)*((2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1) := by
  let D : ℝ := ((J : ℝ)*Real.log 2)^2
  let E : ℝ := (2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1
  have hD : 0 < D := sq_pos_of_pos (mul_pos (by exact_mod_cast hJ) (Real.log_pos (by norm_num)))
  have hφd : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hb (k : ℕ) (hk : k ∈ Icc 1 K) :
      (primePairCofactorCount X (d*k) : ℝ) ≤
        ((X : ℝ)/(450*(d.totient : ℝ)*D))*(if Even k then 1/(k.totient : ℝ) else 0)+E := by
    have hk0 : 0 < k := (mem_Icc.mp hk).1
    by_cases hke : Even k
    · rw [if_pos hke]
      have hφk : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.mpr hk0
      have hφdk : (d.totient : ℝ)*k.totient ≤ (d*k).totient := by
        exact_mod_cast Nat.totient_super_multiplicative d k
      have hp := hmixed X (d*k) (Nat.mul_pos hd hk0)
        ((Nat.mul_le_mul_left d (mem_Icc.mp hk).2).trans hKX)
        ((Nat.mul_le_mul_left d (mem_Icc.mp hk).2).trans hKcap)
      apply hp.trans
      calc
        _ ≤ (X : ℝ)/(450*((d.totient : ℝ)*k.totient)*D)+E := by
          apply _root_.add_le_add _ le_rfl
          apply div_le_div_of_nonneg_left (Nat.cast_nonneg X) (by positivity)
          gcongr
        _ = _ := by ring
    · rw [if_neg hke, mul_zero, zero_add]
      have hodd : Odd (d*k) := hdodd.mul (Nat.not_even_iff_odd.mp hke)
      have hh : (primePairCofactorCount X (d*k) : ℝ) ≤ 1 := by
        exact_mod_cast Sieve.prime_pair_odd_card_le_one (X/(d*k)+1) (d*k)
          (Nat.mul_pos hd hk0) hodd.not_two_dvd_nat
      have hE : (1 : ℝ) ≤ E := by
        have h1 : 0 ≤ (2 : ℝ)^(64*J) := by positivity
        have h2 : 0 ≤ (2 : ℝ)^(16*J) := by positivity
        dsimp [E]
        linarith
      exact hh.trans hE
  calc
    _ ≤ ∑ k ∈ Icc 1 K, (((X : ℝ)/(450*(d.totient : ℝ)*D))*(if Even k then 1/(k.totient : ℝ) else 0)+E) := sum_le_sum hb
    _ = ((X : ℝ)/(450*(d.totient : ℝ)*D))*Sieve.evenReciprocalTotient K + (K : ℝ)*E := by
      rw [sum_add_distrib, ← Finset.mul_sum]
      simp only [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel,
        Sieve.evenReciprocalTotient, Finset.sum_filter]
    _ ≤ ((X : ℝ)/(450*(d.totient : ℝ)*D))*((4/3 : ℝ)*(harmonic K : ℝ)) + (K : ℝ)*E :=
      _root_.add_le_add (mul_le_mul_of_nonneg_left
        (Sieve.even_reciprocal_totient_le_four_thirds_harmonic K) (by positivity)) le_rfl
    _ = _ := by dsimp [D,E]; ring

lemma rough_composite_progression_reciprocal_count_endpoint (X K Y J d : ℕ) (hd : 0 < d) (hdodd : Odd d)
    (hdY : d ∈ Nat.smoothNumbers Y) (hX : X ≤ d*K*Y)
    (hKX : d*K ≤ X) (hKcap : d*K ≤ 2^(256*J)) (hJ : 0 < J) (hmixed : EndpointPairAt J) :
    ((roughProgressionPrimes d Y X).card : ℝ) ≤
      ((2/675 : ℝ)*(X : ℝ)*(harmonic K : ℝ)/((J : ℝ)*Real.log 2)^2) * (d.totient : ℝ)⁻¹ +
      (K : ℝ)*((2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1) := by
  have hc : ((roughProgressionPrimes d Y X).card : ℝ) ≤
      ∑ k ∈ Icc 1 K, (primePairCofactorCount X (d*k) : ℝ) := by
    exact_mod_cast rough_composite_progression_card_le_pairs X K Y d hd hdY hX
  exact hc.trans (sum_prime_pair_composite_cofactor_endpoint X K J d hd hdodd hKX hKcap hJ hmixed)

/-- Unlike the old bound, this does not assume d ≤ 2φ(d). -/
theorem rough_composite_family_reciprocal_count_endpoint (M : Finset ℕ) (D Q X K Y J : ℕ)
    (hM : ∀ d ∈ M, 0 < d ∧ D ≤ d ∧ d ≤ Q ∧ d ∈ Nat.smoothNumbers Y ∧ Odd d)
    (hX : X ≤ D*K*Y) (hKX : Q*K ≤ X) (hQcap : Q*K ≤ 2^(256*J)) (hJ : 0 < J) (hmixed : EndpointPairAt J) :
    (∑ d ∈ M, ((roughProgressionPrimes d Y X).card : ℝ)) ≤
      ((2/675 : ℝ)*(X : ℝ)*(harmonic K : ℝ)/((J : ℝ)*Real.log 2)^2) * (∑ d ∈ M, (d.totient : ℝ)⁻¹) +
      (M.card : ℝ)*K*((2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1) := by
  have hb (d : ℕ) (hd : d ∈ M) := rough_composite_progression_reciprocal_count_endpoint
    X K Y J d (hM d hd).1 (hM d hd).2.2.2.2 (hM d hd).2.2.2.1
    (hX.trans (Nat.mul_le_mul_right Y (Nat.mul_le_mul_right K (hM d hd).2.1)))
    ((Nat.mul_le_mul_right K (hM d hd).2.2.1).trans hKX)
    ((Nat.mul_le_mul_right K (hM d hd).2.2.1).trans hQcap) hJ hmixed
  apply (sum_le_sum hb).trans_eq
  rw [sum_add_distrib, ← mul_sum]
  simp only [sum_const, nsmul_eq_mul]
  ring

end Erdos821.AnalyticSieve
