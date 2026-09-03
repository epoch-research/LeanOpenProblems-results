import Submission.PrimeCurrentL2Convergence
import Submission.UniformPrimeCurrentHead

/-! An explicit subpower rate for the full harmonic prime-current vector.
This does not give the positive-power rate needed for the natural-density
criterion. In particular, the original conjecture is not asserted here. -/

namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable def primeCurrentSquaredError (N : ℕ) : ℝ :=
  ∑' p : ℕ, (rawPrimeWinnerHarmonic p N-primeWinnerHarmonicLimit p)^2

lemma summable_primeCurrentSquaredError (N : ℕ) :
    Summable (fun p : ℕ => (rawPrimeWinnerHarmonic p N-primeWinnerHarmonicLimit p)^2) := by
  exact ((Real.summable_nat_rpow.mpr (by norm_num : (-3/2 : ℝ)< -1)).mul_left
    (4*primeCurrentBudgetConstant^2)).of_norm_bounded
      (harmonic_prime_current_l2_error_bound N)

noncomputable def primeCurrentL2TailConstant : ℝ :=
  4*primeCurrentBudgetConstant^2*(∑' p : ℕ, (p : ℝ)^(-5/4 : ℝ))

lemma primeCurrentL2TailConstant_nonneg : 0 ≤ primeCurrentL2TailConstant := by
  unfold primeCurrentL2TailConstant
  positivity

lemma primeCurrentSquaredError_head_tail (B N : ℕ) :
    primeCurrentSquaredError N ≤ (primeCurrentHeadError B N)^2+
      primeCurrentL2TailConstant*(B+1 : ℝ)^(-1/4 : ℝ) := by
  have hs := summable_primeCurrentSquaredError N
  have hhead : (∑ p ∈ range (B+1),
      (rawPrimeWinnerHarmonic p N-primeWinnerHarmonicLimit p)^2) ≤
        (primeCurrentHeadError B N)^2 := by
    have h := sum_sq_le_sq_sum_of_nonneg (s := range (B+1))
      (fun p _ => norm_nonneg (primeWinnerHarmonicLimit p-rawPrimeWinnerHarmonic p N))
    simpa only [primeCurrentHeadError,Real.norm_eq_abs,sq_abs,sub_sq_comm] using h
  have hr := Real.summable_nat_rpow.mpr (by norm_num : (-5/4 : ℝ)< -1)
  have htail : (∑' j : ℕ,
      (rawPrimeWinnerHarmonic (j+(B+1)) N-primeWinnerHarmonicLimit (j+(B+1)))^2) ≤
        primeCurrentL2TailConstant*(B+1 : ℝ)^(-1/4 : ℝ) := by
    have hpoint (j : ℕ) :
        (rawPrimeWinnerHarmonic (j+(B+1)) N-primeWinnerHarmonicLimit (j+(B+1)))^2 ≤
          (4*primeCurrentBudgetConstant^2*(B+1 : ℝ)^(-1/4 : ℝ))*
            ((j+(B+1) : ℕ) : ℝ)^(-5/4 : ℝ) := by
      have hp : (0 : ℝ)<((j+(B+1) : ℕ) : ℝ) := by positivity
      have h := harmonic_prime_current_l2_error_bound N (j+(B+1))
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)] at h
      have he : (((j+(B+1) : ℕ) : ℝ)^(-3/2 : ℝ)) =
          (((j+(B+1) : ℕ) : ℝ)^(-1/4 : ℝ))*
            (((j+(B+1) : ℕ) : ℝ)^(-5/4 : ℝ)) := by
        rw [← Real.rpow_add hp]
        norm_num
      have hm : (((j+(B+1) : ℕ) : ℝ)^(-1/4 : ℝ)) ≤
          (B+1 : ℝ)^(-1/4 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast (Nat.le_add_left (B+1) j)) (by norm_num)
      rw [he] at h
      calc
        _ ≤ _ := h
        _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hm (by positivity)) (by positivity)
    have hsum := Summable.tsum_le_tsum hpoint ((summable_nat_add_iff (B+1)).mpr hs)
      (((summable_nat_add_iff (B+1)).mpr hr).mul_left
        (4*primeCurrentBudgetConstant^2*(B+1 : ℝ)^(-1/4 : ℝ)))
    rw [tsum_mul_left] at hsum
    have ht : (∑' j : ℕ, (((j+(B+1) : ℕ) : ℝ)^(-5/4 : ℝ))) ≤
        ∑' p : ℕ, (p : ℝ)^(-5/4 : ℝ) := by
      have he := hr.sum_add_tsum_nat_add (B+1)
      have hn : 0 ≤ ∑ p ∈ range (B+1), (p : ℝ)^(-5/4 : ℝ) := by positivity
      linarith
    apply hsum.trans
    calc
      _ ≤ (4*primeCurrentBudgetConstant^2*(B+1 : ℝ)^(-1/4 : ℝ))*
          (∑' p : ℕ, (p : ℝ)^(-5/4 : ℝ)) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by unfold primeCurrentL2TailConstant; ring
  have he := hs.sum_add_tsum_nat_add (B+1)
  change _ = primeCurrentSquaredError N at he
  rw [← he]
  exact add_le_add hhead htail

noncomputable def primeCurrentL2RateConstant : ℝ :=
  (2*Real.exp 4*(1+2/Real.log 2))^2+primeCurrentL2TailConstant

lemma primeCurrentL2RateConstant_pos : 0 < primeCurrentL2RateConstant := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht := primeCurrentL2TailConstant_nonneg
  unfold primeCurrentL2RateConstant
  positivity

lemma primeCurrentSquaredError_exp_scale (N : ℕ) (hN : 0<N)
    (t : ℝ) (ht : 0<t) (ht3 : Real.log 3≤t) (hscale : t^2=Real.log N) :
    primeCurrentSquaredError N ≤
      primeCurrentL2RateConstant*(1+t)^2*Real.exp (-(Real.log 2/32)*t) := by
  let B : ℕ := ⌈Real.exp t⌉₊
  have hB : 0<B := Nat.ceil_pos.mpr (Real.exp_pos t)
  have hB0 : (0 : ℝ)<B+1 := by positivity
  have hfloor : Real.exp t ≤ (B : ℝ) := Nat.le_ceil _
  have hceil : (B : ℝ) < Real.exp t+1 := Nat.ceil_lt_add_one (Real.exp_nonneg t)
  have he1 : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht.le
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hlogB0 : 0<Real.log (B+1 : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1<B+1))
  have hlogB : Real.log (B+1 : ℝ) ≤ 2*t := by
    calc
      _ ≤ Real.log (3*Real.exp t) := Real.log_le_log hB0 (by linarith)
      _ = Real.log 3+t := by rw [Real.log_mul (by norm_num) (Real.exp_ne_zero t),Real.log_exp]
      _ ≤ _ := by linarith
  have hcoef : 1+Real.log (B+1 : ℝ)/Real.log 2 ≤ (1+2/Real.log 2)*(1+t) := by
    have h := div_le_div_of_nonneg_right hlogB hlog.le
    have hp : 0≤2/Real.log 2 := by positivity
    rw [show 2*t/Real.log 2=(2/Real.log 2)*t by ring] at h
    nlinarith
  have hexp : -Real.log 2*Real.log N/(32*Real.log (B+1 : ℝ)) ≤ -(Real.log 2/64)*t := by
    apply (div_le_iff₀ (by positivity : 0<32*Real.log (B+1 : ℝ))).mpr
    rw [← hscale]
    have hh := mul_le_mul_of_nonneg_left hlogB (show 0≤Real.log 2*t by positivity)
    nlinarith
  have hhead : primeCurrentHeadError B N ≤
      (2*Real.exp 4*(1+2/Real.log 2))*(1+t)*Real.exp (-(Real.log 2/64)*t) := by
    apply (primeCurrentHeadError_uniform_bound B N hB hN).trans
    calc
      _ ≤ (2*Real.exp 4*((1+2/Real.log 2)*(1+t)))*
          Real.exp (-(Real.log 2/64)*t) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hcoef (by positivity))
          (Real.exp_le_exp.mpr hexp) (Real.exp_nonneg _) (by positivity)
      _ = _ := by ring
  have hsquare : (primeCurrentHeadError B N)^2 ≤
      (2*Real.exp 4*(1+2/Real.log 2))^2*(1+t)^2*
        Real.exp (-(Real.log 2/32)*t) := by
    have h := pow_le_pow_left₀ (by unfold primeCurrentHeadError; positivity) hhead 2
    apply h.trans_eq
    rw [mul_pow,mul_pow,← Real.exp_nat_mul]
    congr 2
    norm_num
    ring
  have htail : (B+1 : ℝ)^(-1/4 : ℝ) ≤ Real.exp (-(Real.log 2/32)*t) := by
    calc
      _ ≤ (Real.exp t)^(-1/4 : ℝ) := Real.rpow_le_rpow_of_nonpos
        (Real.exp_pos t) (by linarith) (by norm_num)
      _ = Real.exp (-(1/4 : ℝ)*t) := by rw [Real.rpow_def_of_pos (Real.exp_pos t),Real.log_exp]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hl : Real.log 2≤1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)]
        nlinarith
  have hpoly : 1≤(1+t)^2 := by nlinarith
  calc
    _ ≤ (primeCurrentHeadError B N)^2+primeCurrentL2TailConstant*(B+1 : ℝ)^(-1/4 : ℝ) :=
      primeCurrentSquaredError_head_tail B N
    _ ≤ (2*Real.exp 4*(1+2/Real.log 2))^2*(1+t)^2*Real.exp (-(Real.log 2/32)*t)+
        primeCurrentL2TailConstant*(1+t)^2*Real.exp (-(Real.log 2/32)*t) := by
      apply add_le_add hsquare
      calc
        _ ≤ primeCurrentL2TailConstant*Real.exp (-(Real.log 2/32)*t) :=
          mul_le_mul_of_nonneg_left htail primeCurrentL2TailConstant_nonneg
        _ ≤ _ := by
          have hh := mul_le_mul_of_nonneg_left hpoly (show 0≤primeCurrentL2TailConstant*
            Real.exp (-(Real.log 2/32)*t) from mul_nonneg primeCurrentL2TailConstant_nonneg
              (Real.exp_nonneg _))
          convert hh using 1 <;> ring
    _ = _ := by unfold primeCurrentL2RateConstant; ring

/-- An explicit stretched-exponential rate for the whole unweighted
squared error. The factor in front is independent of N. -/
theorem primeCurrentSquaredError_stretched_exp_bound :
    ∀ᶠ N : ℕ in atTop, primeCurrentSquaredError N ≤
      primeCurrentL2RateConstant*Real.exp (-(Real.log 2/64)*Real.sqrt (Real.log N)) := by
  let b : ℝ := Real.log 2/64
  have hb : 0<b := by dsimp [b]; exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have ht : Tendsto (fun N : ℕ => Real.sqrt (Real.log N)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hp (k : ℕ) : Tendsto (fun N : ℕ => (Real.sqrt (Real.log N))^k*
      Real.exp (-b*Real.sqrt (Real.log N))) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast,Function.comp_apply] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) b hb).comp ht
  have hpoly : Tendsto (fun N : ℕ => (1+Real.sqrt (Real.log N))^2*
      Real.exp (-b*Real.sqrt (Real.log N))) atTop (𝓝 0) := by
    have h := ((hp 2).add ((hp 1).const_mul 2)).add (hp 0)
    simp only [add_zero,mul_zero] at h
    convert h using 1
    funext N
    ring
  filter_upwards [eventually_gt_atTop (0 : ℕ),ht.eventually_gt_atTop 0,
    ht.eventually_ge_atTop (Real.log 3),hpoly.eventually_lt_const zero_lt_one] with N hN htN ht3 hsmall
  have h := primeCurrentSquaredError_exp_scale N hN (Real.sqrt (Real.log N)) htN ht3
    (Real.sq_sqrt (Real.log_natCast_nonneg N))
  have he : Real.exp (-(Real.log 2/32)*Real.sqrt (Real.log N)) =
      Real.exp (-b*Real.sqrt (Real.log N))*Real.exp (-b*Real.sqrt (Real.log N)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [b]
    ring
  rw [he] at h
  have hm := mul_le_mul_of_nonneg_right hsmall.le
    (show 0≤primeCurrentL2RateConstant*Real.exp (-b*Real.sqrt (Real.log N)) by
      exact mul_nonneg primeCurrentL2RateConstant_pos.le (Real.exp_nonneg _))
  apply h.trans
  convert hm using 1 <;> ring

/-- In particular, the squared harmonic-current error saves every fixed
power of log N. This is still not a fixed positive-power saving in N. -/
theorem primeCurrentSquaredError_log_power_zero (k : ℕ) :
    Tendsto (fun N : ℕ => (Real.log N)^k*primeCurrentSquaredError N) atTop (𝓝 0) := by
  have hb : 0<Real.log 2/64 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have ht : Tendsto (fun N : ℕ => Real.sqrt (Real.log N)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun N : ℕ => primeCurrentL2RateConstant*(Real.log N)^k*
      Real.exp (-(Real.log 2/64)*Real.sqrt (Real.log N))) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((2*k : ℕ) : ℝ)
      (Real.log 2/64) hb).comp ht).const_mul primeCurrentL2RateConstant
    simp only [mul_zero] at h
    convert h using 1
    funext N
    simp only [Function.comp_apply,Real.rpow_natCast,pow_mul,
      Real.sq_sqrt (Real.log_natCast_nonneg N)]
    ring
  apply squeeze_zero' (Eventually.of_forall (fun N => by
    have hh : 0≤primeCurrentSquaredError N := by unfold primeCurrentSquaredError; positivity
    exact mul_nonneg (pow_nonneg (Real.log_natCast_nonneg N) k) hh)) _ hlim
  filter_upwards [primeCurrentSquaredError_stretched_exp_bound] with N hN
  have h := mul_le_mul_of_nonneg_left hN (pow_nonneg (Real.log_natCast_nonneg N) k)
  convert h using 1
  ring

/-- Scope check for the upper bound, not a lower bound for the actual
current error: its stretched-exponential factor does not beat any fixed
positive power of N. -/
theorem stretched_exp_sqrt_log_times_rpow_atTop (c δ : ℝ) (hδ : 0<δ) :
    Tendsto (fun N : ℕ => (N : ℝ)^δ*Real.exp (-c*Real.sqrt (Real.log N)))
      atTop atTop := by
  have ht : Tendsto (fun N : ℕ => Real.sqrt (Real.log N)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hp : Tendsto (fun N : ℕ => (N : ℝ)^(δ/2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hδ)).comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop_mono' atTop _ hp
  filter_upwards [eventually_gt_atTop (0 : ℕ),ht.eventually_ge_atTop (2*c/δ)] with N hN hlarge
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  have hmul : 2*c ≤ δ*Real.sqrt (Real.log N) := by
    have h := (div_le_iff₀ hδ).mp hlarge
    nlinarith
  have hs := mul_le_mul_of_nonneg_right hmul (Real.sqrt_nonneg (Real.log N))
  have he : Real.sqrt (Real.log N)^2=Real.log N := Real.sq_sqrt (Real.log_natCast_nonneg N)
  rw [Real.rpow_def_of_pos hNr,Real.rpow_def_of_pos hNr,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

#print axioms primeCurrentSquaredError_head_tail
#print axioms primeCurrentSquaredError_stretched_exp_bound
#print axioms primeCurrentSquaredError_log_power_zero
#print axioms stretched_exp_sqrt_log_times_rpow_atTop
end Erdos371
