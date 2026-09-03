import Submission.CofactorMomentSwitching

/-!
# A stronger elementary Mangoldt lower bound

The Chebyshev factorial ratio has coefficients bounded above by one in its
Mangoldt expansion. Stirling's formula gives a lower constant greater than
9/10. This improves a fixed arithmetic lower bound, not the full conjecture.
-/

open Nat Filter ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

lemma chebyshev_floor_kernel_le_one (j : ℕ) :
    (j : ℤ)-(j/2 : ℕ)-(j/3 : ℕ)-(j/5 : ℕ)+(j/30 : ℕ) ≤ 1 := by
  omega

lemma prod_Icc_id_factorial (N : ℕ) : (∏ d ∈ Finset.Icc 1 N, d) = N.factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ, Nat.mul_comm]

lemma log_factorial_eq_mangoldt_floor_sum (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ d ∈ Finset.Icc 1 N, vonMangoldt d * (N/d : ℕ) := by
  have hh := HigherDivisors.sum_convolution_weighted_quotient
    vonMangoldt (ζ : ArithmeticFunction ℝ) (fun _ => 1) N
  rw [vonMangoldt_mul_zeta] at hh
  simp only [log_apply, mul_one] at hh
  have hlog : (∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ)) = Real.log (N.factorial : ℝ) := by
    rw [← Real.log_prod (fun n hn => by
      exact_mod_cast (show n ≠ 0 by have := (Finset.mem_Icc.mp hn).1; omega)),
      ← Nat.cast_prod, prod_Icc_id_factorial]
  rw [hlog] at hh
  refine hh.trans ?_
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  have he (e : ℕ) (he : e ∈ Finset.Icc 1 (N/d)) : (ζ : ArithmeticFunction ℝ) e = 1 := by
    simp [ArithmeticFunction.zeta_apply_ne (show e ≠ 0 by
      have := (Finset.mem_Icc.mp he).1; omega)]
  rw [Finset.sum_congr rfl he]
  simp

lemma log_factorial_eq_mangoldt_floor_sum_of_le (A N : ℕ) (hAN : A ≤ N) :
    Real.log (A.factorial : ℝ) =
      ∑ d ∈ Finset.Icc 1 N, vonMangoldt d * (A/d : ℕ) := by
  rw [log_factorial_eq_mangoldt_floor_sum]
  apply Finset.sum_subset (Finset.Icc_subset_Icc_right hAN)
  intro d hd hdA
  have hAd : A < d := by
    have := (Finset.mem_Icc.mp hd).1
    simp only [Finset.mem_Icc, not_and] at hdA
    exact lt_of_not_ge (hdA this)
  rw [Nat.div_eq_of_lt hAd, Nat.cast_zero, mul_zero]

lemma chebyshev_factorial_ratio_le_mangoldt (N : ℕ) :
    Real.log (N.factorial : ℝ)-Real.log ((N/2).factorial : ℝ)-
      Real.log ((N/3).factorial : ℝ)-Real.log ((N/5).factorial : ℝ)+
      Real.log ((N/30).factorial : ℝ) ≤ mangoldtSum N := by
  rw [log_factorial_eq_mangoldt_floor_sum N,
    log_factorial_eq_mangoldt_floor_sum_of_le (N/2) N (Nat.div_le_self _ _),
    log_factorial_eq_mangoldt_floor_sum_of_le (N/3) N (Nat.div_le_self _ _),
    log_factorial_eq_mangoldt_floor_sum_of_le (N/5) N (Nat.div_le_self _ _),
    log_factorial_eq_mangoldt_floor_sum_of_le (N/30) N (Nat.div_le_self _ _),
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  have h (k : ℕ) : N/k/d=N/d/k := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm k d]
  simp_rw [h]
  have hc : ((N/d : ℕ) : ℝ)-(N/d/2 : ℕ)-(N/d/3 : ℕ)-(N/d/5 : ℕ)+(N/d/30 : ℕ) ≤ 1 := by
    have hh : N/d+N/d/30 ≤ N/d/2+N/d/3+N/d/5+1 := by omega
    have hhR : ((N/d : ℕ) : ℝ)+(N/d/30 : ℕ) ≤
        (N/d/2 : ℕ)+(N/d/3 : ℕ)+(N/d/5 : ℕ)+(1 : ℝ) := by exact_mod_cast hh
    linarith only [hhR]
  have hh := mul_le_mul_of_nonneg_left hc (vonMangoldt_nonneg (n := d))
  convert hh using 1 <;> ring

noncomputable def chebyshevRatioConstant : ℝ :=
  Real.log 30 - (1/2)*Real.log 15 - (1/3)*Real.log 10 - (1/5)*Real.log 6

lemma chebyshevRatioConstant_eq : chebyshevRatioConstant =
    (14/30 : ℝ)*Real.log 2+(9/30 : ℝ)*Real.log 3+(5/30 : ℝ)*Real.log 5 := by
  unfold chebyshevRatioConstant
  rw [show (30 : ℝ)=2*(3*5) by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), show (15 : ℝ)=3*5 by norm_num,
    Real.log_mul (by norm_num) (by norm_num), show (10 : ℝ)=2*5 by norm_num,
    Real.log_mul (by norm_num) (by norm_num), show (6 : ℝ)=2*3 by norm_num,
    Real.log_mul (by norm_num) (by norm_num)]
  ring

lemma nine_tenths_lt_chebyshevRatioConstant : (9/10 : ℝ) < chebyshevRatioConstant := by
  have h6 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 6/5)
  have h5 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 5/4)
  norm_num only [inv_div, invOf_eq_inv] at h6 h5
  have h3 : Real.log 3 = Real.log 2 + Real.log (6/5) + Real.log (5/4) := by
    rw [← Real.log_mul (by norm_num) (by norm_num), ← Real.log_mul (by norm_num) (by norm_num)]
    congr 1
    norm_num
  have h5' : Real.log 5 = 2*Real.log 2 + Real.log (5/4) := by
    have h2 : Real.log ((2 : ℝ)^2) = 2*Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [← h2, ← Real.log_mul (by norm_num) (by norm_num)]
    congr 1
    norm_num
  rw [chebyshevRatioConstant_eq, h3, h5']
  linarith [Real.log_two_gt_d9]


lemma tendsto_log_factorial_multiple_residual (c : ℕ) (hc : 0 < c) :
    Tendsto (fun m : ℕ => Real.log ((c*m).factorial : ℝ)/(m : ℝ)-
      (c : ℝ)*Real.log (m : ℝ)) atTop (𝓝 ((c : ℝ)*Real.log (c : ℝ)-c)) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hcm : Tendsto (fun m : ℕ => c*m) atTop atTop := by
    apply tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m hc) tendsto_id
  have hstir : Tendsto (fun m : ℕ => Real.log (Stirling.stirlingSeq (c*m)))
      atTop (𝓝 (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log (Real.sqrt_pos.mpr Real.pi_pos).ne').tendsto.comp
      (Stirling.tendsto_stirlingSeq_sqrt_pi.comp hcm)
  have hdiv := hstir.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlogdiv : Tendsto (fun m : ℕ => Real.log (m : ℝ)/(m : ℝ)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hconstdiv : Tendsto (fun m : ℕ => Real.log (2*(c : ℝ))/(m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlim := (hdiv.add ((hconstdiv.add hlogdiv).const_mul (1/2))).add_const
    ((c : ℝ)*Real.log (c : ℝ)-c)
  simp only [add_zero, mul_zero, zero_add] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hid := Stirling.log_stirlingSeq_formula (c*m)
  push_cast at hid
  rw [show (2 : ℝ)*((c : ℝ)*m) = (2*(c : ℝ))*(m : ℝ) by ring,
    Real.log_mul (by positivity) hmR.ne', Real.log_div (mul_pos hcR hmR).ne'
      (Real.exp_pos 1).ne', Real.log_mul hcR.ne' hmR.ne', Real.log_exp] at hid
  apply (mul_right_cancel₀ hmR.ne')
  field_simp
  nlinarith only [hid]

noncomputable def chebyshevFactorialRatio (m : ℕ) : ℝ :=
  Real.log ((30*m).factorial : ℝ)-Real.log ((15*m).factorial : ℝ)-
    Real.log ((10*m).factorial : ℝ)-Real.log ((6*m).factorial : ℝ)+
    Real.log (m.factorial : ℝ)

lemma chebyshevFactorialRatio_le_mangoldt (m : ℕ) :
    chebyshevFactorialRatio m ≤ mangoldtSum (30*m) := by
  have hh := chebyshev_factorial_ratio_le_mangoldt (30*m)
  have h2 : 30*m/2=15*m := by omega
  have h3 : 30*m/3=10*m := by omega
  have h5 : 30*m/5=6*m := by omega
  have h30 : 30*m/30=m := by omega
  simpa only [h2, h3, h5, h30, chebyshevFactorialRatio] using hh

lemma tendsto_chebyshevFactorialRatio_div :
    Tendsto (fun m : ℕ => chebyshevFactorialRatio m/(30*(m : ℝ)))
      atTop (𝓝 chebyshevRatioConstant) := by
  have h := (((tendsto_log_factorial_multiple_residual 30 (by decide)).sub
    (tendsto_log_factorial_multiple_residual 15 (by decide))).sub
    (tendsto_log_factorial_multiple_residual 10 (by decide))).sub
    (tendsto_log_factorial_multiple_residual 6 (by decide))
  have h' := (h.add (tendsto_log_factorial_multiple_residual 1 (by decide))).div_const 30
  convert h' using 1
  · funext m
    simp only [Nat.cast_ofNat, Nat.cast_one, one_mul, chebyshevFactorialRatio]
    ring_nf
  · norm_num only [Nat.cast_ofNat, Nat.cast_one, Real.log_one, mul_zero, zero_sub]
    unfold chebyshevRatioConstant
    ring_nf

lemma mangoldtSum_mono : Monotone mangoldtSum := by
  intro A B hAB
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hAB)
    (fun n _ _ => vonMangoldt_nonneg)

/-- A uniform elementary lower bound at every sufficiently large cutoff. -/
theorem eventually_mangoldt_nine_tenths :
    ∀ᶠ N : ℕ in atTop, (9/10 : ℝ)*(N : ℝ) ≤ mangoldtSum N := by
  let c : ℝ := (chebyshevRatioConstant+9/10)/2
  have hclo : (9/10 : ℝ) < c := by
    dsimp [c]
    linarith [nine_tenths_lt_chebyshevRatioConstant]
  have hchi : c < chebyshevRatioConstant := by
    dsimp [c]
    linarith [nine_tenths_lt_chebyshevRatioConstant]
  have hc : 0 < c := by linarith
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (tendsto_chebyshevFactorialRatio_div.eventually (eventually_ge_nhds hchi))
  have hlim : Tendsto (fun N : ℕ => (c-9/10)*(N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by linarith)
  filter_upwards [eventually_ge_atTop (30*(M+1)),
    hlim.eventually (eventually_ge_atTop (30*c))] with N hN hbudget
  let m := N/30
  have hm : M ≤ m := by dsimp [m]; omega
  have hm0 : 0 < m := by dsimp [m]; omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hh : c*(30*(m : ℝ)) ≤ chebyshevFactorialRatio m := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 30*(m : ℝ))).mp (hM m hm)
    exact h
  have hsmall : 30*m ≤ N := Nat.mul_div_le N 30
  have hclose : (N : ℝ)-30 ≤ 30*(m : ℝ) := by
    have hnat : N ≤ 30*m+30 := by dsimp [m]; omega
    have hreal : (N : ℝ) ≤ 30*(m : ℝ)+30 := by exact_mod_cast hnat
    linarith only [hreal]
  have hmain : c*(30*(m : ℝ)) ≤ mangoldtSum N :=
    hh.trans ((chebyshevFactorialRatio_le_mangoldt m).trans (mangoldtSum_mono hsmall))
  have hprod := mul_le_mul_of_nonneg_left hclose hc.le
  nlinarith only [hmain, hprod, hbudget]


end Erdos821.AnalyticSieve
