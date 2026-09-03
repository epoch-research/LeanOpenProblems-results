import Submission.TightIntervalTotient
import Submission.TighterCofactorSieve

/-! # Tight prime-pair block estimates with the sharper even mass -/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

lemma eventually_cofactorBlock_mass_thirteen_tenths (j : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      (∑ k ∈ cofactorBlock j m with Even k, 1/(k.totient : ℝ)) ≤
        (13/10 : ℝ)*(1+64*(m : ℝ)*Real.log 2) := by
  by_cases hj : j=0
  · subst j
    apply Eventually.of_forall
    intro m
    have hset : cofactorBlock 0 m = Icc 1 (2^(64*m)) := by
      ext k
      simp only [cofactorBlock,cofactorBlockEndpoint_zero,cofactorBlockEndpoint_succ,
        zero_add,mul_one,mem_Ioc,mem_Icc]
      omega
    rw [hset]
    apply (Sieve.even_reciprocal_totient_le_thirteen_tenths_harmonic (2^(64*m))).trans
    have hH := harmonic_le_one_add_log (2^(64*m))
    simp only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,Nat.cast_mul] at hH
    nlinarith only [hH]
  · filter_upwards [Sieve.eventually_evenBlockMass_upper_thirteen_tenths j (j+1) (by omega)
      (Nat.le_succ j) 1 (by norm_num)] with m hm
    have hset : cofactorBlock j m = Icc (2^(64*j*m)+1) (2^(64*(j+1)*m)) := by
      ext k
      simp only [cofactorBlock,cofactorBlockEndpoint,if_neg hj,
        if_neg (Nat.succ_ne_zero j),mem_Ioc,mem_Icc]
      omega
    rw [hset]
    change Sieve.evenBlockMass j (j+1) m ≤ _
    simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_left] at hm
    nlinarith only [hm]

lemma eventually_cofactorBlock_mass_thirteen_tenths_all (h : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ j ∈ range h,
      (∑ k ∈ cofactorBlock j m with Even k, 1/(k.totient : ℝ)) ≤
        (13/10 : ℝ)*(1+64*(m : ℝ)*Real.log 2) := by
  rw [eventually_all_finset]
  exact fun j _ => eventually_cofactorBlock_mass_thirteen_tenths j
lemma sum_prime_pair_cofactor_block_ambient_thirteen_tenths (X J d j m : ℕ)
    (hd : 0 < d) (hdodd : Odd d)
    (hX : d*2^(64*(j+1)*m) ≤ X)
    (hmixed : TightEndpointPairUpTo X J)
    (hmass : (∑ k ∈ cofactorBlock j m with Even k, 1/(k.totient : ℝ)) ≤
      (13/10 : ℝ)*(1+64*(m : ℝ)*Real.log 2)) :
    (∑ k ∈ cofactorBlock j m, (primePairCofactorCount X (d*k) : ℝ)) ≤
      ((13/5100 : ℝ)*(X : ℝ)*(1+64*(m : ℝ)*Real.log 2)/((J : ℝ)*Real.log 2)^2)*
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
  apply (sum_prime_pair_cofactor_finset_ambient_tight X J d (cofactorBlock j m) hd hdodd hS hmixed).trans
  calc
    _ ≤ ((X : ℝ)/(510*(d.totient : ℝ)*((J : ℝ)*Real.log 2)^2))*
        ((13/10 : ℝ)*(1+64*(m : ℝ)*Real.log 2))+
          (2 : ℝ)^(64*(j+1)*m)*((2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1) := by
      apply _root_.add_le_add
      · exact mul_le_mul_of_nonneg_left hmass (by positivity)
      · exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring


lemma sum_prime_pair_family_block_ambient_thirteen_tenths (M : Finset ℕ) (X J Q j m : ℕ)
    (hM : ∀ d ∈ M, 0 < d ∧ Odd d ∧ d ≤ Q)
    (hX : Q*2^(64*(j+1)*m) ≤ X)
    (hmixed : TightEndpointPairUpTo X J)
    (hmass : (∑ k ∈ cofactorBlock j m with Even k, 1/(k.totient : ℝ)) ≤
      (13/10 : ℝ)*(1+64*(m : ℝ)*Real.log 2)) :
    (∑ d ∈ M, ∑ k ∈ cofactorBlock j m, (primePairCofactorCount X (d*k) : ℝ)) ≤
      ((13/5100 : ℝ)*(X : ℝ)*(1+64*(m : ℝ)*Real.log 2)/((J : ℝ)*Real.log 2)^2)*
        (∑ d ∈ M, (d.totient : ℝ)⁻¹)+
          (M.card : ℝ)*(2 : ℝ)^(64*(j+1)*m)*((2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1) := by
  have hd (d : ℕ) (hd : d ∈ M) := sum_prime_pair_cofactor_block_ambient_thirteen_tenths X J d j m
    (hM d hd).1 (hM d hd).2.1
    ((Nat.mul_le_mul_right _ (hM d hd).2.2).trans hX)
    hmixed hmass
  apply (sum_le_sum hd).trans_eq
  rw [sum_add_distrib,← mul_sum]
  simp only [sum_const,nsmul_eq_mul]
  ring


end Erdos821.AnalyticSieve
