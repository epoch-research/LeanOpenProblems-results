import Submission.GreedyBatchSquareScales

/-!
The terminal condition in the shrinking-batch certificate limits its time
horizon. These are upper bounds on the numerical output of that certificate,
not upper bounds on the maximum Sidon subset. They do not settle Erdős 773.
-/
namespace Erdos773.GreedyBatchHorizonCeiling
open Filter GreedyBatchProfileStep GreedyBatchDensityProfile
set_option maxHeartbeats 1000000
noncomputable section

lemma a_lower (m : ℕ) (hm : 100 ≤ m) : (1/2 : ℝ) ≤ a m := by
  have hmR : (100 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith only [hmR]
  have hm2 : (10000 : ℝ) ≤ (m : ℝ)^2 := by nlinarith only [hmR]
  have hh : (1000 : ℝ)/(m : ℝ)^2 ≤ 1/2 :=
    (div_le_iff₀ (sq_pos_of_pos hm0)).mpr (by linarith only [hm2])
  dsimp [a]
  linarith only [hh]

/-- Taking logarithms retains the full terminal budget, including its
polynomial reserve. -/
theorem terminal_log_budget {m : ℕ} {d T : ℝ} (hm : 0 < m) (hd : 0 < d)
    (hterminal : (m : ℝ)^1000 ≤ d * Real.exp (-a m*((T+1)^3-1))) :
    a m*((T+1)^3-1) + 1000*Real.log m ≤ Real.log d := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh := Real.log_le_log (pow_pos hmR 1000) hterminal
  rw [Real.log_pow, Real.log_mul hd.ne' (Real.exp_pos _).ne', Real.log_exp] at hh
  norm_num only [Nat.cast_ofNat] at hh
  linarith only [hh]

/-- In particular, an admissible nonnegative horizon has only a logarithmic
cube budget. The decay coefficient does not tend to zero as m grows. -/
theorem horizon_cube_le_two_log {m : ℕ} {d T : ℝ}
    (hm : 100 ≤ m) (hd : 0 < d) (hT : 0 ≤ T)
    (hterminal : (m : ℝ)^1000 ≤ d * Real.exp (-a m*((T+1)^3-1))) :
    T^3 ≤ 2*Real.log d := by
  have ha := a_lower m hm
  have hb := terminal_log_budget (by omega : 0 < m) hd hterminal
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hlog := Real.log_nonneg hm1
  have hE : 0 ≤ (T+1)^3-1 := by nlinarith only [hT, sq_nonneg T]
  have hh := mul_le_mul_of_nonneg_right ha hE
  nlinarith only [hb,hlog,hh,hT,sq_nonneg T]

theorem polynomial_horizon_cube {m : ℕ} {d T X K : ℝ}
    (hm : 100 ≤ m) (hd : 0 < d) (hT : 0 ≤ T) (hX : 0 < X)
    (hdU : d ≤ X^K)
    (hterminal : (m : ℝ)^1000 ≤ d * Real.exp (-a m*((T+1)^3-1))) :
    T^3 ≤ 2*K*Real.log X := by
  have hh := Real.log_le_log hd hdU
  rw [Real.log_rpow hX] at hh
  have ht := horizon_cube_le_two_log hm hd hT hterminal
  nlinarith only [ht,hh]

/-- Uniformly over all admissible m, d, and T with polynomially bounded d,
the time horizon is subpower. -/
theorem eventually_subpower_horizon (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ (m : ℕ) (d T : ℝ),
      100 ≤ m → 0 < d → 1 ≤ T → d ≤ (N : ℝ)^K →
      (m : ℝ)^1000 ≤ d * Real.exp (-a m*((T+1)^3-1)) →
      T ≤ (N : ℝ)^δ := by
  have hh := ((isLittleO_log_rpow_atTop hδ).bound
    (show (0 : ℝ) < 1/(2*K) by positivity))
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hh,
      eventually_ge_atTop (1 : ℕ)] with N hN hN1
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith only [hN1R]
  have hL := Real.log_nonneg hN1R
  simp only [Real.norm_eq_abs, abs_of_nonneg hL,
    abs_of_nonneg (Real.rpow_nonneg hN0.le δ)] at hN
  intro m d T hm hd hT hdU hterminal
  have ht := polynomial_horizon_cube hm hd (by linarith only [hT]) hN0 hdU hterminal
  have hTC : T ≤ T^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hT (by decide : 1 ≤ 3)
  have hmul := mul_le_mul_of_nonneg_left hN (show 0 ≤ 2*K by positivity)
  have he : (2*K)*(1/(2*K)*(N : ℝ)^δ) = (N : ℝ)^δ := by field_simp
  rw [he] at hmul
  nlinarith only [hTC,ht,hmul]

/-- With an additional lower bound d >= N^γ, merely varying the horizon
cannot make the certificate's numerical lower bound exceed N^(1-γ+δ).
This does not preclude choosing an arithmetically better carrier with
smaller d. -/
theorem eventually_output_ceiling (K γ δ : ℝ) (hK : 0 < K) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ (m : ℕ) (d T V : ℝ),
      2000000 ≤ m → (N : ℝ)^γ ≤ d → 1 ≤ T → d ≤ (N : ℝ)^K →
      (m : ℝ)^1000 ≤ d * Real.exp (-a m*((T+1)^3-1)) →
      0 ≤ V → V ≤ N →
      efficiency m*(T-1)/d*V ≤ (N : ℝ)^(1-γ+δ) := by
  filter_upwards [eventually_subpower_horizon K δ hK hδ,
      eventually_ge_atTop (1 : ℕ)] with N hN hN1
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith only [hN1R]
  intro m d T V hm hdL hT hdU hterminal hV0 hVN
  have hp := Real.rpow_pos_of_pos hN0 γ
  have hd := hp.trans_le hdL
  have ht := hN m d T (by omega) hd hT hdU hterminal
  have he := efficiency_bounds m hm
  have htm : 0 ≤ T-1 := by linarith only [hT]
  have hnum : efficiency m*(T-1) ≤ (N : ℝ)^δ := by
    have hh := mul_le_mul_of_nonneg_right he.2 htm
    nlinarith only [hh,ht]
  have hdiv := div_le_div₀ (Real.rpow_nonneg hN0.le δ) hnum hp hdL
  have hmul := mul_le_mul hdiv hVN hV0
    (div_nonneg (Real.rpow_nonneg hN0.le δ) hp.le)
  have hid : (N : ℝ)^δ/(N : ℝ)^γ*N = (N : ℝ)^(1-γ+δ) := by
    rw [← Real.rpow_sub hN0]
    calc
      _ = (N : ℝ)^(δ-γ)*(N : ℝ)^(1 : ℝ) := by rw [Real.rpow_one]
      _ = (N : ℝ)^((δ-γ)+1) := (Real.rpow_add hN0 _ _).symm
      _ = _ := by congr 1; ring
  exact hmul.trans_eq hid

open GreedyBatchSquareScales

lemma eventually_scale_lower (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ)^(1/3-η) ≤ scale N := by
  have hh := ((isLittleO_log_rpow_atTop (show 0 < 3*η/2 by positivity)).bound
    (show (0 : ℝ) < 1/2 by norm_num))
  have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hh,
      ht.eventually (eventually_gt_atTop 0), eventually_ge_atTop (1 : ℕ)] with N hN hL hN1
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith only [hN1R]
  simp only [Real.norm_eq_abs, abs_of_nonneg hL.le,
    abs_of_nonneg (Real.rpow_nonneg hN0.le (3*η/2))] at hN
  have hs := pow_le_pow_left₀ hL.le hN 2
  rw [mul_pow, ← Real.rpow_mul_natCast hN0.le] at hs
  have he : 3*η/2*(2 : ℕ) = 3*η := by norm_num
  rw [he] at hs
  have hs' : (Real.log (N : ℝ))^2 ≤ kappa*(N : ℝ)^(3*η) := by
    have hp := Real.rpow_nonneg hN0.le (3*η)
    dsimp [kappa]
    nlinarith only [hs,hp]
  have hp : (N : ℝ)^(1-3*η)*(N : ℝ)^(3*η) = N := by
    rw [← Real.rpow_add hN0]
    ring_nf
    rw [Real.rpow_one]
  have hm := mul_le_mul_of_nonneg_left hs' (Real.rpow_nonneg hN0.le (1-3*η))
  have hc : (N : ℝ)^(1-3*η) ≤ kappa*N/(Real.log (N : ℝ))^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
    calc
      _ ≤ (N : ℝ)^(1-3*η)*(kappa*(N : ℝ)^(3*η)) := hm
      _ = _ := by rw [← mul_assoc,mul_comm _ kappa,mul_assoc,hp]
  apply le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) (scale_pos hN0 hL).le
  rw [scale_cube hN0.le, ← Real.rpow_mul_natCast hN0.le]
  convert hc using 1
  congr 1
  norm_num
  ring

/-- Keep the endpoint's degree scale, but allow any certificate-admissible
horizon, any m, and even all N available roots. The numerical bound furnished
by that certificate is still below every fixed power above two thirds.
This is not an upper bound on the true Sidon maximum. -/
theorem eventually_endpoint_no_power_gain (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ (m : ℕ) (T V : ℝ),
      2000000 ≤ m → 1 ≤ T →
      (m : ℝ)^1000 ≤ scale N * Real.exp (-a m*((T+1)^3-1)) →
      0 ≤ V → V ≤ N →
      efficiency m*(T-1)/scale N*V < (N : ℝ)^(2/3+δ) := by
  have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_output_ceiling 1 (1/3-δ/4) (δ/4) (by norm_num) (by positivity),
      eventually_scale_lower (δ/4) (by positivity),
      ht.eventually (eventually_ge_atTop 1), eventually_ge_atTop (2 : ℕ)] with N hN hdL hL hN2
  have hN2R : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN1R : (1 : ℝ) ≤ N := by linarith only [hN2R]
  have hdU : scale N ≤ (N : ℝ)^(1 : ℝ) := by
    rw [Real.rpow_one]
    exact scale_upper hN1R hL
  intro m T V hm hT hterminal hV0 hVN
  have hb := hN m (scale N) T V hm hdL hT hdU hterminal hV0 hVN
  apply hb.trans_lt
  apply Real.rpow_lt_rpow_of_exponent_lt (by linarith only [hN2R])
  linarith only [hδ]


#print axioms terminal_log_budget
#print axioms horizon_cube_le_two_log
#print axioms polynomial_horizon_cube
#print axioms eventually_subpower_horizon
#print axioms eventually_output_ceiling
#print axioms eventually_scale_lower
#print axioms eventually_endpoint_no_power_gain
end
end Erdos773.GreedyBatchHorizonCeiling
