import Submission.LogLossSquareCubicArithmetic

/-! Scaling the unconditional logarithmic-loss seed for a conditional
square-cubic iteration. No correlation estimate is proved in this file. -/
namespace Erdos970.GapAverages
open Finset Real Filter
set_option maxHeartbeats 2200000

noncomputable def logIterationSeed (b r t : ℕ) : ℝ :=
  (2 : ℝ)^t/(1600*2^b*(t : ℝ)^b*(logIterationRoot r t : ℝ)^8)

lemma logIterationSeed_pos (b r t : ℕ) (ht : 0 < t) : 0 < logIterationSeed b r t := by
  have hq0 : (0 : ℝ) < logIterationRoot r t := by exact_mod_cast (logIterationRoot_bounds r t ht).1
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  unfold logIterationSeed
  positivity

lemma logIteration_loss_le_seed (C : ℝ) (hC : 0 ≤ C) (b r t : ℕ) (ht : 0 < t)
    (hcost : 1600*2^b*C ≤ (t : ℝ)*log (2 : ℝ)^(b+8*r+1)) :
    C*(2 : ℝ)^t/log ((2 : ℝ)^t)^(b+8*r+1) ≤ logIterationSeed b r t := by
  have hq0 : (0 : ℝ) < logIterationRoot r t := by exact_mod_cast (logIterationRoot_bounds r t ht).1
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hq : (logIterationRoot r t : ℝ) ≤ (t : ℝ)^r := by
    exact_mod_cast (logIterationRoot_bounds r t ht).2.1
  have hq8 := pow_le_pow_left₀ hq0.le hq 8
  have h1 := mul_le_mul_of_nonneg_left hq8
    (show 0 ≤ 1600*2^b*C*(t : ℝ)^b by positivity)
  have h2 := mul_le_mul_of_nonneg_right hcost
    (show 0 ≤ (t : ℝ)^(b+8*r) by positivity)
  have hpre : C*(1600*2^b*(t : ℝ)^b*(logIterationRoot r t : ℝ)^8) ≤
      log ((2 : ℝ)^t)^(b+8*r+1) := by
    calc
      _ ≤ 1600*2^b*C*(t : ℝ)^b*((t : ℝ)^r)^8 := by convert h1 using 1 <;> ring
      _ = 1600*2^b*C*(t : ℝ)^(b+8*r) := by
        rw [pow_add,pow_mul]
        ring
      _ ≤ ((t : ℝ)*log (2 : ℝ)^(b+8*r+1))*(t : ℝ)^(b+8*r) := h2
      _ = _ := by rw [log_pow,mul_pow,pow_succ]; ring
  unfold logIterationSeed
  apply (div_le_div_iff₀ (by rw [log_pow]; positivity)
    (by positivity : 0 < 1600*2^b*(t : ℝ)^b*(logIterationRoot r t : ℝ)^8)).mpr
  have hh := mul_le_mul_of_nonneg_left hpre (show 0 ≤ (2 : ℝ)^t by positivity)
  convert hh using 1 <;> ring

lemma logIteration_seed_le_void_rate (b r t : ℕ) (ht : 0 < t)
    (hidx : 64*logIterationIndex r t ≤ t) :
    2*logIterationSeed b r t ≤
      sqrt (logIterationLength r t : ℝ)/(800*log (logIterationLength r t : ℝ)^b) := by
  have hq0 : (0 : ℝ) < logIterationRoot r t := by exact_mod_cast (logIterationRoot_bounds r t ht).1
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hbudget := (logIterationLength_budget r t hidx).1
  have hK : 2 ≤ (2 : ℕ)^t := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) (show 1 ≤ t from ht)
  have hM : (1 : ℝ) < logIterationLength r t := by
    have hh : (2 : ℝ) ≤ logIterationLength r t := by exact_mod_cast hK.trans hbudget
    linarith only [hh]
  have hL : 0 < log (logIterationLength r t : ℝ) := log_pos hM
  have hlog := pow_le_pow_left₀ hL.le (logIterationLength_log r t) b
  rw [mul_pow] at hlog
  have hsqrt := logIterationLength_sqrt r t hidx
  have he : 2*logIterationSeed b r t =
      (2*(2 : ℝ)^t)/(1600*2^b*(t : ℝ)^b*(logIterationRoot r t : ℝ)^8) := by
    unfold logIterationSeed
    ring
  rw [he]
  apply (div_le_div_iff₀ (by positivity : 0 < 1600*2^b*(t : ℝ)^b*(logIterationRoot r t : ℝ)^8)
    (by positivity : 0 < 800*log (logIterationLength r t : ℝ)^b)).mpr
  have hh := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 1600*(2 : ℝ)^t by positivity)
  calc
    _ = (1600*(2 : ℝ)^t)*log (logIterationLength r t : ℝ)^b := by ring
    _ ≤ (1600*(2 : ℝ)^t)*(2^b*(t : ℝ)^b) := hh
    _ = _ := by rw [← hsqrt]; ring

lemma eventually_logIteration_loss_cost (C : ℝ) (b r : ℕ) :
    ∀ᶠ t : ℕ in atTop, 1600*2^b*C ≤ (t : ℝ)*log (2 : ℝ)^(b+8*r+1) := by
  have hL : 0 < log (2 : ℝ)^(b+8*r+1) := pow_pos (log_pos (by norm_num)) _
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop ((1600*2^b*C)/log (2 : ℝ)^(b+8*r+1)))] with t ht
  exact (div_le_iff₀ hL).mp ht

/-- The unconditional seed absorbs a factor exp(C*k/log(k)^B) at the
shorter starting interval, with B=b+8r+1. -/
theorem eventually_logIteration_scaled_seed (b r : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hseed : ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      coveredFraction P k ≤ exp (-sqrt (k : ℝ)/(800*log (k : ℝ)^b))) :
    ∀ᶠ t : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ 2^t →
      exp (C*(2 : ℝ)^t/log ((2 : ℝ)^t)^(b+8*r+1))*
        coveredFraction P (logIterationLength r t) ≤ exp (-logIterationSeed b r t) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hseed
  have hg := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))).eventually
    (eventually_ge_atTop N)
  filter_upwards [eventually_logIterationIndex_small r,eventually_logIteration_loss_cost C b r,
    hg,eventually_ge_atTop 1] with t hidx hcost hNt ht
  intro P hP hPk
  have hKm := (logIterationLength_budget r t hidx).1
  have hvoid := hN _ (hNt.trans hKm) P hP (hPk.trans hKm)
  have hloss := logIteration_loss_le_seed C hC b r t ht hcost
  have hrate := logIteration_seed_le_void_rate b r t ht hidx
  apply (mul_le_mul_of_nonneg_left hvoid (exp_pos _).le).trans
  rw [← exp_add]
  apply exp_le_exp.mpr
  simp only [neg_div] at ⊢
  linarith only [hloss,hrate]

#print axioms eventually_logIteration_scaled_seed
end Erdos970.GapAverages
