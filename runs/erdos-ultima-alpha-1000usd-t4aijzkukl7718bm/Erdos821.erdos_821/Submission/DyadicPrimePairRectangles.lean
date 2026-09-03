import Submission.DyadicSuccessorScales

/-!
# Prime-pair rectangles at all sufficiently large dyadic cutoffs

The leading coefficient 2*t/b approaches four as the strict half-level
margin shrinks. The lower cofactor-length exponent can simultaneously be
made arbitrarily small by fixing a=1 and l=3 and increasing b.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

theorem eventually_dyadic_prime_pair_rectangles (a b t l : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ b) (ht : 22 ≤ t) (hlevel : 2*b+5 ≤ t) (hl : 2*a+1 ≤ l)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, ∀ A B c M N : ℕ, 0 < c → 2^(k-1) ≤ M → M ≤ N → N ≤ 2^k →
      cofactorScale l (2*cofactorDyadicIndex t k) ≤ B-A →
        ((cofactorPrimePairPool c A B M N).card : ℝ) ≤
          (2*(t : ℝ)/(b : ℝ))*((B-A : ℕ) : ℝ)*(mangoldtSum N-mangoldtSum M)*
            ((c : ℝ)/(c.totient : ℝ))/(((k : ℝ)*Real.log 2)*Real.log (M : ℝ))+
              δ*((B-A : ℕ) : ℝ)*(2 : ℝ)^k/(((k : ℝ)+1)*Real.log (M : ℝ)) := by
  obtain ⟨K,hK,HK⟩ := exists_cofactor_interval_successor_power_saving a b t l ha hab ht hlevel hl
  filter_upwards [eventually_dyadic_sieve_error t (by omega) K δ hK.le hδ,
    eventually_ge_atTop (512*t+2)] with k hkerr hk
  intro A B c M N hc hM hMN hN hAB
  let m := cofactorDyadicIndex t k
  let z := cofactorScale b m
  have hzM : z ≤ M := (cofactor_dyadic_sift_below b t k (by omega) (by omega) (by omega)).trans hM
  have hM2 : 2 ≤ M := by
    apply le_trans _ hM
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 1 ≤ k-1 by omega)
    simpa only [pow_one] using hp
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (show 1<M by omega))
  have hkR : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have htR : (0 : ℝ)<t := by exact_mod_cast (show 0<t by omega)
  have hbR : (0 : ℝ)<b := by exact_mod_cast (show 0<b by omega)
  have hlog2 : (0 : ℝ)<Real.log 2 := Real.log_pos (by norm_num)
  have hlogbase : 0 < ((b : ℝ)/(2*(t : ℝ)))*((k : ℝ)*Real.log 2) := by positivity
  have hlog := cofactor_dyadic_log_lower b t k (by omega)
  have hinv := one_div_le_one_div_of_le hlogbase hlog
  have he : 1/(((b : ℝ)/(2*(t : ℝ)))*((k : ℝ)*Real.log 2)) =
      (2*(t : ℝ)/(b : ℝ))/((k : ℝ)*Real.log 2) := by field_simp
  rw [he] at hinv
  have hmass : 0 ≤ mangoldtSum N-mangoldtSum M := sub_nonneg.mpr
    (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hMN) (fun _ _ _ => vonMangoldt_nonneg))
  have hmain := mul_le_mul_of_nonneg_left hinv
    (show 0 ≤ ((B-A : ℕ) : ℝ)*(mangoldtSum N-mangoldtSum M)*((c : ℝ)/(c.totient : ℝ)) by positivity)
  have herr := mul_le_mul_of_nonneg_left hkerr (Nat.cast_nonneg (B-A))
  have hsieve := HK m A B c M N hc hMN (hN.trans (cofactor_dyadic_ambient_bounds t k (by omega)).1) hAB
  have hbound : cofactorIntervalPrimeSuccessorWeight c A B M N z ≤
      (2*(t : ℝ)/(b : ℝ))*((B-A : ℕ) : ℝ)*(mangoldtSum N-mangoldtSum M)*
        ((c : ℝ)/(c.totient : ℝ))/((k : ℝ)*Real.log 2)+
          δ*((B-A : ℕ) : ℝ)*(2 : ℝ)^k/((k : ℝ)+1) := by
    apply hsieve.trans
    convert _root_.add_le_add hmain herr using 1 <;> dsimp [z,m] <;> ring
  apply (cofactor_prime_pair_count_le_weight c A B M N z hc hM2 hzM).trans
  apply (div_le_div_of_nonneg_right hbound hlogM.le).trans_eq
  rw [add_div,div_div,div_div]

end Erdos821.AnalyticSieve
