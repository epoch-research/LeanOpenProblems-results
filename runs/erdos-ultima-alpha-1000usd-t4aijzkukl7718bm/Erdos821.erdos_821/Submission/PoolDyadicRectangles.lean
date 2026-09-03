import Submission.PoolPrimeRectangles
import Submission.DyadicSuccessorScales

/-!
# Pool rectangles on every dyadic scale

An arbitrary logarithmic saving is retained in the ambient error, so it
can subsequently be summed over both prime and multiplier blocks.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

lemma eventually_dyadic_pool_sieve_error (t w : ℕ) (ht : 1 ≤ t) (K δ : ℝ)
    (hK : 0 ≤ K) (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop,
      K*((cofactorDyadicIndex t k : ℝ)+1)^7/(2 : ℝ)^(cofactorDyadicIndex t k)*
        (cofactorScale t (2*cofactorDyadicIndex t k) : ℝ) ≤
          δ*(2 : ℝ)^k/((k : ℝ)+1)^w := by
  let D : ℝ := K*(2 : ℝ)^(512*t)*(512*(t : ℝ)+1)^w
  have hlim := (Erdos821.tendsto_succ_pow_div_two_pow (7+w)).const_mul D
  simp only [mul_zero] at hlim
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hlim.eventually (eventually_le_nhds hδ))
  filter_upwards [cofactorDyadicIndex_eventually_ge_pos t M ht] with k hk
  let m := cofactorDyadicIndex t k
  have hm := hM m hk
  have hbase : (cofactorScale t (2*m) : ℝ) ≤ (2 : ℝ)^(512*t)*(2 : ℝ)^k := by
    exact_mod_cast (cofactor_dyadic_ambient_bounds t k ht).2
  have hkm : (k : ℝ)+1 ≤ (512*(t : ℝ)+1)*((m : ℝ)+1) := by
    have hh : (k : ℝ) ≤ 512*(t : ℝ)*(m : ℝ) := by
      exact_mod_cast (cofactorDyadicIndex_bounds t k ht).1.le
    nlinarith only [hh,Nat.cast_nonneg (α := ℝ) m,Nat.cast_nonneg (α := ℝ) t]
  apply (le_div_iff₀ (by positivity : (0 : ℝ)<((k : ℝ)+1)^w)).mpr
  have hp : 0 ≤ K*((m : ℝ)+1)^7/(2 : ℝ)^m := by positivity
  have hscale := mul_le_mul hbase (pow_le_pow_left₀ (by positivity) hkm w)
    (by positivity : (0 : ℝ) ≤ ((k : ℝ)+1)^w) (by positivity)
  have hprod := mul_le_mul_of_nonneg_left hscale hp
  have hlast := mul_le_mul_of_nonneg_right hm (show (0 : ℝ) ≤ 2^k by positivity)
  apply le_trans ?_ hlast
  convert hprod using 1 <;> dsimp [D,m] <;> (try simp only [pow_add,mul_pow]) <;> ring

/-- The sieve-prime cutoff can exceed sqrt(2^k), provided it remains
strictly below the prime-variable interval. -/
lemma eventually_cofactor_dyadic_sift_below (b t : ℕ) (ht : 1 ≤ t) (hbt : b < 2*t) :
    ∀ᶠ k : ℕ in atTop, cofactorScale b (cofactorDyadicIndex t k) ≤ 2^(k-1) := by
  filter_upwards [eventually_ge_atTop (512*b*t+2*t)] with k hk
  have hh := Nat.mul_le_mul_left b (cofactorDyadicIndex_bounds t k ht).2
  have hg := Nat.mul_le_mul_right k (Nat.succ_le_iff.mpr hbt)
  have hk0 : 1 ≤ k := by nlinarith only [hk,ht,Nat.zero_le (512*b*t)]
  have he : 256*b*cofactorDyadicIndex t k ≤ k-1 := by
    apply Nat.le_of_mul_le_mul_left (c := 2*t) _ (by omega)
    have hsub := Nat.sub_add_cancel hk0
    nlinarith only [hh,hg,hk,hsub]
  rw [cofactorScale_eq]
  exact Nat.pow_le_pow_right (by decide) he

/-- The large-conductor lengths use D*B. The error has no factor #P. -/
theorem eventually_dyadic_pool_prime_rectangles (a b s l v t w : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hs : 2*a+1 ≤ s)
    (hl : 1 ≤ l) (ht : 1 ≤ t) (hbt : b < 2*t) (hlevel : 2*b+1 ≤ l+t)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, ∀ D B M N : ℕ,
      2^(k-1) ≤ M → M ≤ N → N ≤ 2^k →
      cofactorScale s (2*cofactorDyadicIndex t k) ≤ B →
      cofactorScale l (2*cofactorDyadicIndex t k) ≤ D*B →
      D*B ≤ cofactorScale v (2*cofactorDyadicIndex t k) →
      ∀ P : Finset ℕ, P ⊆ Icc 1 D →
      (∀ c ∈ P, ∀ p : ℕ, p.Prime → p ≤ cofactorScale b (cofactorDyadicIndex t k) → ¬p ∣ c) →
      ((poolPrimePairPool P 0 B M N).card : ℝ) ≤
        (2*(t : ℝ)/(b : ℝ))*(P.card : ℝ)*(B : ℝ)*(mangoldtSum N-mangoldtSum M)/
          (((k : ℝ)*Real.log 2)*Real.log (M : ℝ))+
            δ*((D*B : ℕ) : ℝ)*(2 : ℝ)^k/(((k : ℝ)+1)^w*Real.log (M : ℝ)) := by
  obtain ⟨K,hK,HK⟩ := exists_pool_prime_rectangle_power_saving a b s l v t ha hab hs hl ht hlevel
  filter_upwards [eventually_dyadic_pool_sieve_error t w ht K δ hK.le hδ,
    eventually_cofactor_dyadic_sift_below b t ht hbt,
    eventually_ge_atTop 2] with k hkerr hcut hk
  intro D B M N hM hMN hN hB hDB hDBup P hP hrough
  let m := cofactorDyadicIndex t k
  let z := cofactorScale b m
  have hzM : z ≤ M := hcut.trans hM
  have hM2 : 2 ≤ M := by
    apply le_trans _ hM
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 1 ≤ k-1 by omega)
    simpa only [pow_one] using hp
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (show 1<M by omega))
  have hbR : (0 : ℝ)<b := by exact_mod_cast (ha.trans hab)
  have htR : (0 : ℝ)<t := by exact_mod_cast ht
  have hkR : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hlog2 : (0 : ℝ)<Real.log 2 := Real.log_pos (by norm_num)
  have hlogbase : 0 < ((b : ℝ)/(2*(t : ℝ)))*((k : ℝ)*Real.log 2) := by positivity
  have hinv := one_div_le_one_div_of_le hlogbase (cofactor_dyadic_log_lower b t k ht)
  have he : 1/(((b : ℝ)/(2*(t : ℝ)))*((k : ℝ)*Real.log 2)) =
      (2*(t : ℝ)/(b : ℝ))/((k : ℝ)*Real.log 2) := by field_simp
  rw [he] at hinv
  have hmass : 0 ≤ mangoldtSum N-mangoldtSum M := sub_nonneg.mpr
    (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hMN) (fun _ _ _ => vonMangoldt_nonneg))
  have hmain := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hinv
    (show 0 ≤ (P.card : ℝ)*(B : ℝ)*(mangoldtSum N-mangoldtSum M) by positivity)) hlogM.le
  have herr := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hkerr (Nat.cast_nonneg (D*B))) hlogM.le
  have hsieve := HK m D B M N hMN hB hDB hDBup
    (hN.trans (cofactor_dyadic_ambient_bounds t k ht).1) hM2 hzM P hP hrough
  apply hsieve.trans
  convert _root_.add_le_add hmain herr using 1 <;> dsimp [m,z] <;> ring

end Erdos821.AnalyticSieve
