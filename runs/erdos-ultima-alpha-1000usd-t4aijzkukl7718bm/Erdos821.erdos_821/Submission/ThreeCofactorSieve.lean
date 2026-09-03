import Submission.ThreePrimePairBound
import Submission.ThreeCofactorMass

/-! # Prime-pair cofactor sums with the local correction retained -/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

lemma eventually_cofactorBlock_corrected_mass (j : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      (∑ k ∈ cofactorBlock j m with Even k, Sieve.threeCorrection k/(k.totient : ℝ)) ≤
        (39/35 : ℝ)*(1+64*(m : ℝ)*Real.log 2) := by
  by_cases hj : j=0
  · subst j
    filter_upwards [eventually_ge_atTop 1] with m hm
    let B := 2^(64*m-1)
    have he : 2*B=2^(64*m) := Sieve.two_mul_pow_pred_eq _ (by omega)
    have hset : cofactorBlock 0 m = Icc (2*0+1) (2*B) := by
      rw [he]
      ext k
      simp only [cofactorBlock,cofactorBlockEndpoint_zero,cofactorBlockEndpoint_succ,
        zero_add,mul_one,mul_zero,mem_Ioc,mem_Icc]
      omega
    rw [hset,Sieve.sum_even_interval_eq_double]
    simp only [zero_add]
    apply (Sieve.corrected_reciprocal_totient_double_prefix B).trans
    have hH := harmonic_le_one_add_log B
    have hlog : Real.log (B : ℝ) ≤ 64*(m : ℝ)*Real.log 2 := by
      simp only [B,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
      have hh : ((64*m-1 : ℕ) : ℝ) ≤ 64*(m : ℝ) := by exact_mod_cast Nat.sub_le (64*m) 1
      exact mul_le_mul_of_nonneg_right hh (Real.log_pos (by norm_num)).le
    linarith only [hH,hlog]
  · filter_upwards [Sieve.eventually_correctedEvenBlockMass_upper j (j+1) (by omega)
      (Nat.le_succ j) 1 (by norm_num)] with m hm
    have hset : cofactorBlock j m = Icc (2^(64*j*m)+1) (2^(64*(j+1)*m)) := by
      ext k
      simp only [cofactorBlock,cofactorBlockEndpoint,if_neg hj,
        if_neg (Nat.succ_ne_zero j),mem_Ioc,mem_Icc]
      omega
    rw [hset]
    change Sieve.correctedEvenBlockMass j (j+1) m ≤ _
    simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_left] at hm
    nlinarith only [hm]

lemma eventually_cofactorBlock_corrected_mass_all (h : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ j ∈ range h,
      (∑ k ∈ cofactorBlock j m with Even k, Sieve.threeCorrection k/(k.totient : ℝ)) ≤
        (39/35 : ℝ)*(1+64*(m : ℝ)*Real.log 2) := by
  rw [eventually_all_finset]
  exact fun j _ => eventually_cofactorBlock_corrected_mass j

lemma prime_pair_cofactor_odd_modulus_ambient_three (X J d k : ℕ)
    (hd : 0 < d) (hdodd : Odd d) (hd3 : ¬3 ∣ d) (hk : 0 < k)
    (hdX : d*k ≤ X) (hmixed : ThreeEndpointPairUpTo X J) :
    (primePairCofactorCount X (d*k) : ℝ) ≤
      ((X : ℝ)/(510*(d.totient : ℝ)*((J : ℝ)*Real.log 2)^2))*
        (if Even k then Sieve.threeCorrection k/(k.totient : ℝ) else 0)+
          ((2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1) := by
  by_cases hke : Even k
  · rw [if_pos hke]
    have hphi : (d.totient : ℝ)*k.totient ≤ (d*k).totient := by
      exact_mod_cast Nat.totient_super_multiplicative d k
    have hpd : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
    have hpk : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.mpr hk
    have he := Sieve.threeCorrection_mul_of_not_dvd d k hd3
    have hc : 0 < Sieve.threeCorrection k := lt_of_lt_of_le (by norm_num) (Sieve.threeCorrection_bounds k).1
    apply (hmixed (d*k) (Nat.mul_pos hd hk) hdX).trans
    by_cases hJ : J=0
    · subst J
      simp
    have hD : 0 < ((J : ℝ)*Real.log 2)^2 :=
      sq_pos_of_pos (mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hJ)
        (Real.log_pos (by norm_num)))
    rw [he]
    calc
      _ ≤ Sieve.threeCorrection k*(X : ℝ)/(510*((d.totient : ℝ)*k.totient)*((J : ℝ)*Real.log 2)^2)+
          ((2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1) := by
        apply _root_.add_le_add _ le_rfl
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        gcongr
      _ = _ := by ring
  · rw [if_neg hke,mul_zero,zero_add]
    have hodd : Odd (d*k) := hdodd.mul (Nat.not_even_iff_odd.mp hke)
    have hh : (primePairCofactorCount X (d*k) : ℝ) ≤ 1 := by
      exact_mod_cast Sieve.prime_pair_odd_card_le_one (X/(d*k)+1) (d*k)
        (Nat.mul_pos hd hk) hodd.not_two_dvd_nat
    exact hh.trans (by
      have h1 : 0 ≤ (2 : ℝ)^(64*J) := by positivity
      have h2 : 0 ≤ (2 : ℝ)^(16*J) := by positivity
      linarith only [h1,h2])


lemma sum_prime_pair_cofactor_finset_ambient_three (X J d : ℕ) (S : Finset ℕ)
    (hd : 0 < d) (hdodd : Odd d) (hd3 : ¬3 ∣ d)
    (hS : ∀ k ∈ S, 0 < k ∧ d*k ≤ X)
    (hmixed : ThreeEndpointPairUpTo X J) :
    (∑ k ∈ S, (primePairCofactorCount X (d*k) : ℝ)) ≤
      ((X : ℝ)/(510*(d.totient : ℝ)*((J : ℝ)*Real.log 2)^2))*
        (∑ k ∈ S with Even k, Sieve.threeCorrection k/(k.totient : ℝ))+
          (S.card : ℝ)*((2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1) := by
  apply (sum_le_sum (fun k hk => prime_pair_cofactor_odd_modulus_ambient_three
    X J d k hd hdodd hd3 (hS k hk).1 (hS k hk).2 hmixed)).trans_eq
  rw [sum_add_distrib,← mul_sum,sum_filter]
  simp only [sum_const,nsmul_eq_mul]


lemma sum_prime_pair_cofactor_block_ambient_three (X J d j m : ℕ)
    (hd : 0 < d) (hdodd : Odd d) (hd3 : ¬3 ∣ d)
    (hX : d*2^(64*(j+1)*m) ≤ X)
    (hmixed : ThreeEndpointPairUpTo X J)
    (hmass : (∑ k ∈ cofactorBlock j m with Even k, Sieve.threeCorrection k/(k.totient : ℝ)) ≤
      (39/35 : ℝ)*(1+64*(m : ℝ)*Real.log 2)) :
    (∑ k ∈ cofactorBlock j m, (primePairCofactorCount X (d*k) : ℝ)) ≤
      ((13/5950 : ℝ)*(X : ℝ)*(1+64*(m : ℝ)*Real.log 2)/((J : ℝ)*Real.log 2)^2)*
        (d.totient : ℝ)⁻¹+
          (2 : ℝ)^(64*(j+1)*m)*((2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1) := by
  have hS (k : ℕ) (hk : k ∈ cofactorBlock j m) :
      0 < k ∧ d*k ≤ X := by
    have hk' := mem_Ioc.mp hk
    rw [cofactorBlockEndpoint_succ] at hk'
    exact ⟨lt_of_le_of_lt (Nat.zero_le _) hk'.1,
      (Nat.mul_le_mul_left d hk'.2).trans hX⟩
  have hcard : ((cofactorBlock j m).card : ℝ) ≤ (2 : ℝ)^(64*(j+1)*m) := by
    have hc : (cofactorBlock j m).card ≤ 2^(64*(j+1)*m) := by
      simp only [cofactorBlock,Nat.card_Ioc,cofactorBlockEndpoint_succ]
      exact Nat.sub_le _ _
    exact_mod_cast hc
  apply (sum_prime_pair_cofactor_finset_ambient_three X J d (cofactorBlock j m) hd hdodd hd3 hS hmixed).trans
  calc
    _ ≤ ((X : ℝ)/(510*(d.totient : ℝ)*((J : ℝ)*Real.log 2)^2))*
        ((39/35 : ℝ)*(1+64*(m : ℝ)*Real.log 2))+
          (2 : ℝ)^(64*(j+1)*m)*((2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1) := by
      apply _root_.add_le_add
      · exact mul_le_mul_of_nonneg_left hmass (by positivity)
      · exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring


lemma sum_prime_pair_family_block_ambient_three (M : Finset ℕ) (X J Q j m : ℕ)
    (hM : ∀ d ∈ M, 0 < d ∧ Odd d ∧ d ≤ Q ∧ ¬3 ∣ d)
    (hX : Q*2^(64*(j+1)*m) ≤ X)
    (hmixed : ThreeEndpointPairUpTo X J)
    (hmass : (∑ k ∈ cofactorBlock j m with Even k, Sieve.threeCorrection k/(k.totient : ℝ)) ≤
      (39/35 : ℝ)*(1+64*(m : ℝ)*Real.log 2)) :
    (∑ d ∈ M, ∑ k ∈ cofactorBlock j m, (primePairCofactorCount X (d*k) : ℝ)) ≤
      ((13/5950 : ℝ)*(X : ℝ)*(1+64*(m : ℝ)*Real.log 2)/((J : ℝ)*Real.log 2)^2)*
        (∑ d ∈ M, (d.totient : ℝ)⁻¹)+
          (M.card : ℝ)*(2 : ℝ)^(64*(j+1)*m)*((2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1) := by
  have hd (d : ℕ) (hd : d ∈ M) := sum_prime_pair_cofactor_block_ambient_three X J d j m
    (hM d hd).1 (hM d hd).2.1 (hM d hd).2.2.2
    ((Nat.mul_le_mul_right _ (hM d hd).2.2.1).trans hX)
    hmixed hmass
  apply (sum_le_sum hd).trans_eq
  rw [sum_add_distrib,← mul_sum]
  simp only [sum_const,nsmul_eq_mul]
  ring



end Erdos821.AnalyticSieve
