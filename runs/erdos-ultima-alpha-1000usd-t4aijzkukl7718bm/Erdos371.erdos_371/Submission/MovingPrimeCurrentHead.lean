import Submission.UniformPrimeCurrentHead
import Submission.DyadicSeriesTools

/-! An explicit cutoff tending to infinity for which all smaller harmonic
prime-current limits are approximated simultaneously in l1. The large-prime
current tail is not controlled by this result. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma double_power_current_head_bound (j N : ℕ) (hN : 0<N)
    (hsize : 64*(j+1 : ℝ)*(2 : ℝ)^j*Real.log 2≤Real.log N) :
    primeCurrentHeadError (2^(2^j)-1) N ≤ Real.exp 4*(1/2 : ℝ)^j := by
  have hpow1 : (1 : ℕ)<2^(2^j) := Nat.one_lt_pow (by positivity) (by norm_num)
  have hB : 0<2^(2^j)-1 := by omega
  have hB1 : 2^(2^j)-1+1=(2 : ℕ)^(2^j) := by omega
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hp0 : (0 : ℝ)<2^j := by positivity
  have hlog : Real.log ((2^(2^j)-1 : ℕ)+1 : ℝ) = (2 : ℝ)^j*Real.log 2 := by
    rw [← Nat.cast_add_one,hB1,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
    push_cast
    rfl
  have hb := primeCurrentHeadError_uniform_bound (2^(2^j)-1) N hB hN
  rw [hlog] at hb
  have hcancel : 1+((2 : ℝ)^j*Real.log 2)/Real.log 2 = 1+2^j := by
    field_simp
  rw [hcancel] at hb
  have hexp : -Real.log 2*Real.log N/(32*((2 : ℝ)^j*Real.log 2)) ≤
      -(2*(j+1 : ℝ)*Real.log 2) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<32*((2 : ℝ)^j*Real.log 2))).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsize hl2.le]
  have hp1 : (1 : ℝ)≤2^j := one_le_pow₀ (by norm_num)
  have hcoef : 2*Real.exp 4*(1+(2 : ℝ)^j) ≤ 4*Real.exp 4*(2 : ℝ)^j := by
    nlinarith [Real.exp_pos 4]
  calc
    _ ≤ 2*Real.exp 4*(1+(2 : ℝ)^j)*Real.exp (-(2*(j+1 : ℝ)*Real.log 2)) :=
      hb.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity))
    _ ≤ 4*Real.exp 4*(2 : ℝ)^j*Real.exp (-(2*(j+1 : ℝ)*Real.log 2)) :=
      mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
    _ = Real.exp 4*(1/2 : ℝ)^j := by
      have h2pow : (2 : ℝ)^j = Real.exp ((j : ℝ)*Real.log 2) := by
        rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
      have h4 : (4 : ℝ)=Real.exp (2*Real.log 2) := by
        rw [show (2 : ℝ)=(2 : ℕ) by norm_num,Real.exp_nat_mul,Real.exp_log (by norm_num)]
        norm_num
      have hhalf : (1/2 : ℝ)^j = Real.exp (-((j : ℝ)*Real.log 2)) := by
        rw [Real.exp_neg,← h2pow]
        simp only [one_div,inv_pow]
      rw [hhalf,h2pow]
      nth_rw 1 [h4]
      rw [show Real.exp (2*Real.log 2)*Real.exp 4*Real.exp ((j : ℝ)*Real.log 2)*
          Real.exp (-(2*(j+1 : ℝ)*Real.log 2)) =
          Real.exp 4*(Real.exp (2*Real.log 2)*Real.exp ((j : ℝ)*Real.log 2)*
            Real.exp (-(2*(j+1 : ℝ)*Real.log 2))) by ring,
        ← Real.exp_add,← Real.exp_add]
      congr 2
      ring

def currentHeadBandIndex (k : ℕ) : ℕ :=
  Nat.findGreatest (fun j => 64*(j+1)*2^j≤k) k

lemma currentHeadBandIndex_budget (k : ℕ) (hk : 64≤k) :
    64*(currentHeadBandIndex k+1)*2^(currentHeadBandIndex k)≤k :=
  Nat.findGreatest_spec (P := fun j => 64*(j+1)*2^j≤k) (m := 0)
    (by omega) (by norm_num; exact hk)

lemma currentHeadBandIndex_tendsto : Tendsto currentHeadBandIndex atTop atTop := by
  apply tendsto_atTop.mpr
  intro j
  filter_upwards [eventually_ge_atTop (max j (64*(j+1)*2^j))] with k hk
  apply Nat.le_findGreatest
  · exact (le_max_left _ _).trans hk
  · exact (le_max_right _ _).trans hk

def movingCurrentHeadCutoff (N : ℕ) : ℕ :=
  2^(2^(currentHeadBandIndex (Nat.log 2 N)))-1

lemma movingCurrentHeadCutoff_tendsto : Tendsto movingCurrentHeadCutoff atTop atTop := by
  have h := currentHeadBandIndex_tendsto.comp nat_log_two_tendsto
  apply tendsto_atTop_mono _ h
  intro N
  let j := currentHeadBandIndex (Nat.log 2 N)
  have h1 := Nat.lt_two_pow_self (n := j)
  have h2 := Nat.lt_two_pow_self (n := 2^j)
  change j≤2^(2^j)-1
  omega

lemma movingCurrentHeadError_eventual_bound :
    ∀ᶠ N : ℕ in atTop, primeCurrentHeadError (movingCurrentHeadCutoff N) N ≤
      Real.exp 4*(1/2 : ℝ)^(currentHeadBandIndex (Nat.log 2 N)) := by
  filter_upwards [nat_log_two_tendsto.eventually_ge_atTop 64,eventually_gt_atTop (0 : ℕ)]
    with N hk hN
  let k := Nat.log 2 N
  let j := currentHeadBandIndex k
  apply double_power_current_head_bound j N hN
  have hbudget : 64*(j+1 : ℝ)*(2 : ℝ)^j≤k := by
    exact_mod_cast currentHeadBandIndex_budget k hk
  have hl2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog := Real.log_le_log (by positivity : (0 : ℝ)<(2 : ℝ)^k)
    (show (2 : ℝ)^k≤N by exact_mod_cast Nat.pow_log_le_self 2 hN.ne')
  rw [Real.log_pow] at hlog
  exact (mul_le_mul_of_nonneg_right hbudget hl2).trans hlog

/-- All labels up to this growing cutoff converge simultaneously in the
unnormalized l1 error. The cutoff is not held fixed before the limit. -/
theorem moving_prime_current_head_error_tendsto_zero :
    Tendsto (fun N => primeCurrentHeadError (movingCurrentHeadCutoff N) N)
      atTop (𝓝 0) := by
  have hgeo := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (1/2 : ℝ)<1)).comp
      (currentHeadBandIndex_tendsto.comp nat_log_two_tendsto)
  have h := hgeo.const_mul (Real.exp 4)
  simp only [mul_zero] at h
  apply squeeze_zero' _ movingCurrentHeadError_eventual_bound h
  exact Eventually.of_forall (fun N => by unfold primeCurrentHeadError; positivity)

#print axioms movingCurrentHeadCutoff_tendsto
#print axioms moving_prime_current_head_error_tendsto_zero
end Erdos371
