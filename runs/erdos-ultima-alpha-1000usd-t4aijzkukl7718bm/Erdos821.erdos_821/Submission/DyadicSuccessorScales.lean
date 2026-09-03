import Submission.CofactorPrimePairCover

/-!
# Interpolating the successor sieve to every dyadic exponent

The ambient scale exceeds the desired dyadic cutoff by a fixed factor,
not by a factor exponential in the running exponent. This fixed loss is
absorbed into the exponentially decaying error.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

def cofactorDyadicIndex (t k : ℕ) : ℕ := k/(512*t)+1

lemma cofactorDyadicIndex_bounds (t k : ℕ) (ht : 1 ≤ t) :
    k < 512*t*cofactorDyadicIndex t k ∧
      512*t*cofactorDyadicIndex t k ≤ k+512*t := by
  have hd : 0 < 512*t := by omega
  have hlo := (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (k/(512*t)))
  have hhi := Nat.div_mul_le_self k (512*t)
  dsimp only [cofactorDyadicIndex]
  constructor <;> nlinarith only [hlo,hhi]

lemma cofactorDyadicIndex_eventually_ge_pos (t K : ℕ) (ht : 1 ≤ t) :
    ∀ᶠ k : ℕ in atTop, K ≤ cofactorDyadicIndex t k := by
  have hd : 0 < 512*t := by omega
  filter_upwards [eventually_ge_atTop (K*(512*t))] with k hk
  have hh := (Nat.le_div_iff_mul_le hd).mpr hk
  exact hh.trans (Nat.le_succ _)

lemma cofactor_dyadic_ambient_bounds (t k : ℕ) (ht : 1 ≤ t) :
    2^k ≤ cofactorScale t (2*cofactorDyadicIndex t k) ∧
      cofactorScale t (2*cofactorDyadicIndex t k) ≤ 2^(512*t)*2^k := by
  have hh := cofactorDyadicIndex_bounds t k ht
  have he : cofactorScale t (2*cofactorDyadicIndex t k) =
      2^(512*t*cofactorDyadicIndex t k) := by
    unfold cofactorScale progressionScaleN
    congr 1
    ring
  rw [he,← pow_add]
  exact ⟨Nat.pow_le_pow_right (by decide) hh.1.le,
    Nat.pow_le_pow_right (by decide) (by omega)⟩

lemma cofactor_dyadic_sift_below (b t k : ℕ) (ht : 1 ≤ t) (hbt : b ≤ t)
    (hk : 512*t<k) :
    cofactorScale b (cofactorDyadicIndex t k) ≤ 2^(k-1) := by
  have hh := (cofactorDyadicIndex_bounds t k ht).2
  have hbm := Nat.mul_le_mul_right (512*cofactorDyadicIndex t k) hbt
  have hk1 : k-1+1=k := Nat.sub_add_cancel (by omega)
  have he : 256*b*cofactorDyadicIndex t k ≤ k-1 := by nlinarith only [hh,hbm,hk,hk1]
  have hz : cofactorScale b (cofactorDyadicIndex t k)=2^(256*b*cofactorDyadicIndex t k) := by
    unfold cofactorScale progressionScaleN
    congr 1
    ring
  rw [hz]
  exact Nat.pow_le_pow_right (by decide) he

lemma cofactor_dyadic_log_lower (b t k : ℕ) (ht : 1 ≤ t) :
    ((b : ℝ)/(2*(t : ℝ)))*((k : ℝ)*Real.log 2) ≤
      Real.log ((cofactorScale b (cofactorDyadicIndex t k) : ℝ)+1) := by
  have htR : (0 : ℝ)<t := by exact_mod_cast ht
  have hkm : (k : ℝ) ≤ 512*(t : ℝ)*(cofactorDyadicIndex t k : ℝ) := by
    exact_mod_cast (cofactorDyadicIndex_bounds t k ht).1.le
  have hb : 0 ≤ (b : ℝ)/(2*(t : ℝ)) := by positivity
  have hlog0 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkm hb) hlog0
  have he : ((b : ℝ)/(2*(t : ℝ)))*(512*(t : ℝ)*(cofactorDyadicIndex t k : ℝ))*Real.log 2 =
      256*(b : ℝ)*(cofactorDyadicIndex t k : ℝ)*Real.log 2 := by field_simp; ring
  rw [he,← cofactorScale_log] at hh
  have hmono := Real.log_le_log
    (by exact_mod_cast cofactorScale_pos b (cofactorDyadicIndex t k) :
      (0 : ℝ)<cofactorScale b (cofactorDyadicIndex t k))
    (show (cofactorScale b (cofactorDyadicIndex t k) : ℝ) ≤
      (cofactorScale b (cofactorDyadicIndex t k) : ℝ)+1 by linarith)
  simpa only [mul_assoc] using hh.trans hmono

lemma eventually_dyadic_sieve_error (t : ℕ) (ht : 1 ≤ t) (K δ : ℝ)
    (hK : 0 ≤ K) (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop,
      K*((cofactorDyadicIndex t k : ℝ)+1)^6/(2 : ℝ)^(cofactorDyadicIndex t k)*
        (cofactorScale t (2*cofactorDyadicIndex t k) : ℝ) ≤
          δ*(2 : ℝ)^k/((k : ℝ)+1) := by
  let D : ℝ := K*(2 : ℝ)^(512*t)*(512*(t : ℝ)+1)
  have hlim := (Erdos821.tendsto_succ_pow_div_two_pow 7).const_mul D
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
  apply (le_div_iff₀ (by positivity : (0 : ℝ)<(k : ℝ)+1)).mpr
  have hp : 0 ≤ K*((m : ℝ)+1)^6/(2 : ℝ)^m := by positivity
  have hscale := mul_le_mul hbase hkm (by positivity : (0 : ℝ) ≤ (k : ℝ)+1) (by positivity)
  have hprod := mul_le_mul_of_nonneg_left hscale hp
  have hlast := mul_le_mul_of_nonneg_right hm (show (0 : ℝ) ≤ 2^k by positivity)
  apply le_trans ?_ hlast
  convert hprod using 1 <;> dsimp [D,m] <;> ring

end Erdos821.AnalyticSieve
