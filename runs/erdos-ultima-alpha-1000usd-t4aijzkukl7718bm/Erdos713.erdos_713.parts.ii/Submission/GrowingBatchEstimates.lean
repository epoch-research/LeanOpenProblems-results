import FormalConjecturesUtil
import Submission.SafeBatchAsymptotics

/-! Uniform estimates for genuinely growing merger batches. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical Topology
namespace Erdos713GrowingBatchEstimates
open Erdos713DegreePenalty Erdos713DegreePenaltySupports Erdos713MergeDegreePenalty
open Erdos713CommonBlockerPairCount Erdos713SafeMergeBatch
set_option maxHeartbeats 2000000

lemma eventually_power_comparison {a b C ε : ℝ} (hab : a < b) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, C*(n : ℝ)^a < ε*(n : ℝ)^b := by
  have ht : Tendsto (fun n : ℕ => C*(n : ℝ)^(a-b)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [neg_sub,mul_zero] using
      (((tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp
        tendsto_natCast_atTop_atTop).const_mul C)
  filter_upwards [ht.eventually_lt_const hε,eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hp : (n : ℝ)^(a-b)*(n : ℝ)^b=(n : ℝ)^a := by
    rw [← Real.rpow_add hnR,sub_add_cancel]
  have hh := mul_lt_mul_of_pos_right hn (Real.rpow_pos_of_pos hnR b)
  simpa only [mul_assoc,hp] using hh

lemma eventually_lossBound {β δ C K ε : ℝ}
    (hβ : 0 ≤ β) (hK : 0 ≤ K)
    (hgap : δ+4*β < 1) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k D : ℕ,
      (k : ℝ) ≤ K*(n : ℝ)^δ → (D : ℝ) ≤ C*(n : ℝ)^β →
      ((k*lossBound n D : ℕ) : ℝ) ≤ ε*(n : ℝ)^2 := by
  filter_upwards [eventually_power_comparison (C := K*(96*C^4+5))
    (show 1+4*β+δ < 2 by linarith) hε,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  intro k D hk hD
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have hp : 1 ≤ (n : ℝ)^(4*β) := Real.one_le_rpow hnR (by positivity)
  have hDp : (D : ℝ)^4 ≤ C^4*(n : ℝ)^(4*β) := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) D) hD 4
    rw [mul_pow,← Real.rpow_mul_natCast hn0.le] at hh
    convert hh using 1
    congr 2
    ring
  have hnPow : (n : ℝ)*(n : ℝ)^(4*β)=(n : ℝ)^(1+4*β) := by
    rw [Real.rpow_add hn0,Real.rpow_one]
  have hL : (lossBound n D : ℝ) ≤ (96*C^4+5)*(n : ℝ)^(1+4*β) := by
    have hm := mul_le_mul_of_nonneg_left hDp (show 0 ≤ 96*(n : ℝ) by positivity)
    have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ 5*(n : ℝ) by positivity)
    rw [← hnPow]
    dsimp only [lossBound]
    push_cast
    nlinarith only [hm,hp',hnR]
  have hkp : 0 ≤ K*(n : ℝ)^δ := mul_nonneg hK (Real.rpow_nonneg hn0.le _)
  have hm := mul_le_mul hk hL (Nat.cast_nonneg (lossBound n D)) hkp
  have hp' : (n : ℝ)^δ*(n : ℝ)^(1+4*β)=(n : ℝ)^(1+4*β+δ) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  have he : (K*(n : ℝ)^δ)*((96*C^4+5)*(n : ℝ)^(1+4*β))=
      K*(96*C^4+5)*(n : ℝ)^(1+4*β+δ) := by
    calc
      _ = K*(96*C^4+5)*((n : ℝ)^δ*(n : ℝ)^(1+4*β)) := by ring
      _ = _ := by rw [hp']
  rw [he] at hm
  have hm' : ((k*lossBound n D : ℕ) : ℝ) ≤
      K*(96*C^4+5)*(n : ℝ)^(1+4*β+δ) := by
    simpa only [Nat.cast_mul] using hm
  exact hm'.trans (by simpa only [Real.rpow_two] using hn.le)

lemma batch_slope {n k : ℕ} {b p t mu : ℝ} (hk0 : 0 < k) (hkn : k ≤ n)
    (hb : 0 < b) (hp : 0 < p) (hmu : 0 ≤ mu)
    (hSlope : b*p ≤ mu*(2*n-1))
    (hLoss : t ≤ (k : ℝ)*b/8*p) (hSmall : (k : ℝ) ≤ b/8*p) :
    t+(k : ℝ)*(b/4*p)+(k : ℝ)*(k-1)/2 < mu*(2*n*k-(k : ℝ)^2) := by
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hprod := mul_nonneg hkR.le (sub_nonneg.mpr hknR)
  have hRatio : (k : ℝ)/2*(2*n-1) ≤ 2*n*k-(k : ℝ)^2 := by
    nlinarith only [hprod,hkR]
  have hRat := mul_le_mul_of_nonneg_left hRatio hmu
  have hSl := mul_le_mul_of_nonneg_left hSlope (show 0 ≤ (k : ℝ)/2 by positivity)
  have hSm := mul_le_mul_of_nonneg_left hSmall hkR.le
  have hpos : 0 < (k : ℝ)*b*p := by positivity
  nlinarith only [hRat,hSl,hSm,hLoss,hpos,hkR]

/-- k is chosen from n, not fixed before taking the limit. The bound on k
and the common-loss comparison hold uniformly over the penalty mu. -/
lemma eventually_batch {A b β δ : ℝ} (hA : 0 < A) (hb : 0 < b)
    (hδ : 0 ≤ δ) (hδβ : δ < β) (hδ1 : δ < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, ∃ k : ℕ,
      (k : ℝ) ≤ K*(n : ℝ)^δ ∧ ∀ mu : ℝ, 0 ≤ mu →
        b*(n : ℝ)^β ≤ mu*(2*n-1) →
        A*(n : ℝ)^(β+δ)+(k : ℝ)*(b/4*(n : ℝ)^β)+(k : ℝ)*(k-1)/2 <
          mu*(2*n*k-(k : ℝ)^2) := by
  let C : ℝ := 8*A/b+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C+1,by positivity,?_⟩
  filter_upwards [eventually_power_comparison (C := C+1) hδβ (show 0 < b/8 by positivity),
    eventually_power_comparison (C := C+1) hδ1 (show (0 : ℝ) < 1 by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n hSmall hOrder hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have hpn : 1 ≤ (n : ℝ)^δ := Real.one_le_rpow hnR hδ
  have hp : 0 < (n : ℝ)^β := Real.rpow_pos_of_pos hn0 _
  let k : ℕ := ⌈C*(n : ℝ)^δ⌉₊
  have hLower : C*(n : ℝ)^δ ≤ (k : ℝ) := Nat.le_ceil _
  have hUpper : (k : ℝ) ≤ (C+1)*(n : ℝ)^δ := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ C*(n : ℝ)^δ by positivity)
    change (k : ℝ) < C*(n : ℝ)^δ+1 at hh
    nlinarith only [hh,hpn]
  have hk0 : 0 < k := by
    have hh : (0 : ℝ) < k := (mul_pos hC (Real.rpow_pos_of_pos hn0 _)).trans_le hLower
    exact_mod_cast hh
  have hkn : k ≤ n := by
    have hh := hUpper.trans hOrder.le
    simpa only [Real.rpow_one,one_mul,Nat.cast_le] using hh
  refine ⟨k,hUpper,?_⟩
  intro mu hmu hSlope
  apply batch_slope hk0 hkn hb hp hmu hSlope _ (hUpper.trans hSmall.le)
  have hCb : A ≤ C*b/8 := by dsimp [C]; field_simp; nlinarith
  have hm := mul_le_mul_of_nonneg_right hLower (show 0 ≤ b/8*(n : ℝ)^β by positivity)
  have hp' : (n : ℝ)^(β+δ)=(n : ℝ)^δ*(n : ℝ)^β := by
    rw [Real.rpow_add hn0,mul_comm]
  have hm' := mul_le_mul_of_nonneg_right hCb (Real.rpow_nonneg hn0.le (β+δ))
  rw [hp'] at hm' ⊢
  nlinarith only [hm,hm']

#print axioms eventually_lossBound
#print axioms batch_slope
#print axioms eventually_batch
end Erdos713GrowingBatchEstimates
