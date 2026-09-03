import Submission.SharpSmoothMangoldt
import Submission.SelbergLowerMain

/-! Positive convolution majorants and joint-parameter L1 estimates.
These estimates do not assert a prime-pair lower bound. -/
namespace Erdos972JointSmoothL1
open Finset ArithmeticFunction Filter
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta Topology
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive
open Erdos972SharpSmoothMangoldt Erdos972DivisorEnergy
open Erdos972SelbergLowerMain Erdos972ChebyshevRowMean
set_option autoImplicit false
set_option maxHeartbeats 1500000

noncomputable def twist (t : ℝ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  f.pmul (expWeight t)

lemma twist_mul (t : ℝ) (f g : ArithmeticFunction ℝ) :
    twist t (f*g) = twist t f * twist t g := by
  ext n
  simp only [twist, pmul_apply, ArithmeticFunction.mul_apply, sum_mul]
  apply sum_congr rfl
  intro ab hab
  have h := Nat.mem_divisorsAntidiagonal.mp hab
  have ha : ab.1 ≠ 0 := by intro hh; simp [hh] at h; exact h.2 h.1.symm
  have hb : ab.2 ≠ 0 := by intro hh; simp [hh] at h; exact h.2 h.1.symm
  have hn : n ≠ 0 := h.2
  simp only [expWeight, coe_mk, if_neg ha, if_neg hb, if_neg hn]
  rw [← h.1, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr ha) (Nat.cast_ne_zero.mpr hb),
    mul_add, Real.exp_add]
  ring

lemma moebius_log_identity :
    -(ArithmeticFunction.pmul (μ : ArithmeticFunction ℝ) log) = (μ : ArithmeticFunction ℝ)*Λ := by
  have he : -(ArithmeticFunction.pmul (μ : ArithmeticFunction ℝ) log)*ζ = Λ := by
    ext n
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    change (∑ d ∈ n.divisors, -((μ d : ℝ)*log d)) = Λ n
    rw [sum_neg_distrib, sum_moebius_mul_log_eq, neg_neg]
  calc
    _ = (-(ArithmeticFunction.pmul (μ : ArithmeticFunction ℝ) log)*ζ)*μ := by
      rw [mul_assoc, coe_zeta_mul_coe_moebius, mul_one]
    _ = _ := by rw [he, mul_comm]

noncomputable def divisorAF (t : ℝ) : ArithmeticFunction ℝ := twist t μ * ζ
noncomputable def derivativeAF (t : ℝ) : ArithmeticFunction ℝ := divisorAF t * twist t Λ
noncomputable def majorant (t : ℝ) : ArithmeticFunction ℝ := divisorAF t * Λ

lemma majorant_eq (t : ℝ) : majorant t = twist t μ * log := by
  unfold majorant divisorAF
  rw [mul_assoc, zeta_mul_vonMangoldt]

lemma divisorAF_apply (t : ℝ) (n : ℕ) : divisorAF t n = expDivisorSum t n :=
  (expDivisorSum_eq t n).symm

lemma derivativeAF_apply (t : ℝ) (n : ℕ) :
    derivativeAF t n = ∑ d ∈ n.divisors, -(μ d : ℝ)*Real.log d*Real.exp (-t*Real.log d) := by
  have he : derivativeAF t = twist t (-(ArithmeticFunction.pmul (μ : ArithmeticFunction ℝ) log))*ζ := by
    rw [moebius_log_identity, twist_mul]
    unfold derivativeAF divisorAF
    ac_rfl
  rw [he, ArithmeticFunction.coe_mul_zeta_apply]
  apply sum_congr rfl
  intro d hd
  change (-((μ d : ℝ)*Real.log d))*(expWeight t d) = _
  simp only [expWeight, coe_mk, if_neg (Nat.pos_of_mem_divisors hd).ne']
  ring

lemma hasDerivAt_divisorAF (t : ℝ) (n : ℕ) :
    HasDerivAt (fun s => divisorAF s n) (derivativeAF t n) t := by
  simp only [divisorAF_apply, derivativeAF_apply, expDivisorSum]
  apply HasDerivAt.fun_sum
  intro d hd
  convert ((((hasDerivAt_id t).neg.mul_const (Real.log d)).exp).const_mul (μ d : ℝ)) using 1
  simp [Pi.neg_apply]
  ring

lemma divisorAF_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ divisorAF t n := by
  rw [divisorAF_apply]
  exact expDivisorSum_nonneg ht n

lemma twist_mangoldt_bounds {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ twist t Λ n ∧ twist t Λ n ≤ Λ n := by
  by_cases hn : n = 0
  · subst n; simp
  have he : Real.exp (-t*Real.log n) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (Real.log_natCast_nonneg n))
  simp only [twist, pmul_apply, expWeight, coe_mk, if_neg hn]
  exact ⟨mul_nonneg vonMangoldt_nonneg (Real.exp_pos _).le,
    (mul_le_mul_of_nonneg_left he vonMangoldt_nonneg).trans_eq (mul_one _)⟩

lemma derivativeAF_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ derivativeAF t n := by
  unfold derivativeAF
  rw [ArithmeticFunction.mul_apply]
  exact sum_nonneg fun _ _ => mul_nonneg (divisorAF_nonneg ht _) (twist_mangoldt_bounds ht _).1

noncomputable def harmonicDivisorMass (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 N, divisorAF t n/n

noncomputable def harmonicDerivativeMass (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 N, derivativeAF t n/n

lemma mass_deriv (N : ℕ) (t : ℝ) :
    HasDerivAt (harmonicDivisorMass N) (harmonicDerivativeMass N t) t := by
  unfold harmonicDivisorMass harmonicDerivativeMass
  exact HasDerivAt.fun_sum fun n hn => (hasDerivAt_divisorAF t n).div_const n

lemma mass_nonneg (N : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ harmonicDivisorMass N t :=
  sum_nonneg fun n _hn => div_nonneg (divisorAF_nonneg ht n) (Nat.cast_nonneg n)

lemma derivative_mass_nonneg (N : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ harmonicDerivativeMass N t :=
  sum_nonneg fun n _hn => div_nonneg (derivativeAF_nonneg ht n) (Nat.cast_nonneg n)

lemma mass_at_zero {N : ℕ} (hN : 0 < N) : harmonicDivisorMass N 0 = 1 := by
  classical
  simp only [harmonicDivisorMass, divisorAF_apply, expDivisorSum_at_zero, one_apply]
  rw [sum_eq_single 1]
  · simp
  · intro n hn hn1
    simp [hn1]
  · simp [hN.ne']

lemma derivative_mass_le (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    harmonicDerivativeMass N t ≤ (14*(1+Real.log N))*harmonicDivisorMass N t := by
  have hh := reciprocal_sum_convolution_le (divisorAF t) (twist t Λ)
    (divisorAF_nonneg ht) (fun n => (twist_mangoldt_bounds ht n).1) N
  have hb : (∑ n ∈ Ioc 0 N, twist t Λ n/n) ≤ 14*(1+Real.log N) := by
    apply le_trans _ (reciprocal_mangoldt_bound N)
    exact sum_le_sum fun n hn => div_le_div_of_nonneg_right (twist_mangoldt_bounds ht n).2
      (Nat.cast_nonneg n)
  exact hh.trans ((mul_le_mul_of_nonneg_left hb (mass_nonneg N ht)).trans_eq (mul_comm _ _))

/-- An all-cutoff bound that permits t to depend on N. -/
theorem harmonic_mass_bound {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t) :
    harmonicDivisorMass N t ≤ Real.exp (14*(1+Real.log N)*t) := by
  have hh := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := harmonicDivisorMass N) (f' := harmonicDerivativeMass N)
    (δ := 1) (K := 14*(1+Real.log N)) (ε := 0) (a := 0) (b := t)
    (continuous_iff_continuousAt.mpr (fun s => (mass_deriv N s).continuousAt)).continuousOn
    (fun s hs => (mass_deriv N s).hasDerivWithinAt)
    (by rw [mass_at_zero hN]; norm_num)
    (by
      intro s hs
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (derivative_mass_nonneg N hs.1),
        abs_of_nonneg (mass_nonneg N hs.1), add_zero]
      exact derivative_mass_le N hs.1) t ⟨ht, le_rfl⟩
  simpa only [Real.norm_eq_abs, abs_of_nonneg (mass_nonneg N ht), sub_zero,
    gronwallBound_ε0, one_mul] using hh

lemma divisorAF_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (n : ℕ) :
    divisorAF s n ≤ divisorAF t n := by
  by_cases hn : n = 0
  · subst n; simp
  simp only [divisorAF_apply, expDivisorSum_product _ hn]
  apply prod_le_prod (fun p hp => expFactor_nonneg hs p)
  intro p hp
  apply sub_le_sub_left
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hst (Real.log_natCast_nonneg p)]

lemma derivative_le_majorant {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (n : ℕ) :
    derivativeAF s n ≤ majorant t n := by
  simp only [derivativeAF, majorant, ArithmeticFunction.mul_apply]
  apply sum_le_sum
  intro ab hab
  exact mul_le_mul (divisorAF_mono hs hst ab.1) (twist_mangoldt_bounds hs ab.2).2
    (twist_mangoldt_bounds hs ab.2).1 (divisorAF_nonneg (hs.trans hst) ab.1)

lemma smooth_le_majorant {t : ℝ} (ht : 0 < t) (n : ℕ) :
    smoothMangoldt t n ≤ majorant t n := by
  obtain ⟨c, hc, he⟩ := exists_hasDerivAt_eq_slope (fun s => divisorAF s n)
    (fun s => derivativeAF s n) ht
    (continuous_iff_continuousAt.mpr (fun s => (hasDerivAt_divisorAF s n).continuousAt)).continuousOn
    (fun s hs => hasDerivAt_divisorAF s n)
  have hb := derivative_le_majorant hc.1.le hc.2.le n
  rw [he] at hb
  simpa only [divisorAF_apply, sub_zero, smoothMangoldt] using hb

noncomputable def excessAF (t : ℝ) : ArithmeticFunction ℝ := divisorAF t - 1

lemma excessAF_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ excessAF t n := by
  change 0 ≤ divisorAF t n - (1 : ArithmeticFunction ℝ) n
  by_cases hn : n = 1
  · subst n
    simp [divisorAF_apply, expDivisorSum]
  · simp only [one_apply, if_neg hn, sub_zero]
    exact divisorAF_nonneg ht n

lemma majorant_excess (t : ℝ) : majorant t - Λ = excessAF t * Λ := by
  unfold majorant excessAF
  rw [sub_mul, one_mul]

lemma mangoldt_le_majorant {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : Λ n ≤ majorant t n := by
  apply sub_nonneg.mp
  change 0 ≤ (majorant t - Λ) n
  rw [majorant_excess, ArithmeticFunction.mul_apply]
  exact sum_nonneg fun ab hab => mul_nonneg (excessAF_nonneg ht ab.1) vonMangoldt_nonneg

lemma reciprocal_excess {N : ℕ} (hN : 0 < N) (t : ℝ) :
    (∑ n ∈ Ioc 0 N, excessAF t n/n) = harmonicDivisorMass N t - 1 := by
  have hz : (∑ n ∈ Ioc 0 N, (1 : ArithmeticFunction ℝ) n/n) = 1 := by
    simpa only [harmonicDivisorMass, divisorAF_apply, expDivisorSum_at_zero] using mass_at_zero hN
  change (∑ n ∈ Ioc 0 N, (divisorAF t n - (1 : ArithmeticFunction ℝ) n)/n) = _
  simp only [sub_div, sum_sub_distrib, hz]
  rfl

lemma sum_convolution_mangoldt_le (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (f*Λ) n) ≤ 7*N*(∑ n ∈ Ioc 0 N, f n/n) := by
  simp only [ArithmeticFunction.mul_apply]
  rw [sum_divisorsAntidiagonal_eq_sum_hyperbola (fun a b => f a*Λ b) N, mul_sum]
  apply sum_le_sum
  intro a ha
  rw [← mul_sum]
  have hpsi : (∑ b ∈ Ioc 0 (N/a), Λ b) = Chebyshev.psi (N/a : ℕ) := by
    simp [Chebyshev.psi]
  rw [hpsi]
  have hdiv : ((N/a : ℕ) : ℝ) ≤ (N : ℝ)/a := by
    apply (le_div_iff₀ (Nat.cast_pos.mpr (mem_Ioc.mp ha).1)).mpr
    exact_mod_cast Nat.div_mul_le_self N a
  calc
    _ ≤ f a * (7*(N/a : ℕ)) := mul_le_mul_of_nonneg_left
      (psi_le_seven_mul (Nat.cast_nonneg _)) (hf a)
    _ ≤ f a * (7*((N : ℝ)/a)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hdiv (by norm_num)) (hf a)
    _ = _ := by ring

/-- The genuine nonnegative majorant excess has a uniform joint bound. -/
theorem majorant_excess_sum_bound {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t) :
    (∑ n ∈ Ioc 0 N, (majorant t n - Λ n)) ≤
      7*N*(Real.exp (14*(1+Real.log N)*t)-1) := by
  have he : (∑ n ∈ Ioc 0 N, (majorant t n - Λ n)) =
      ∑ n ∈ Ioc 0 N, (excessAF t*Λ) n := by
    change (∑ n ∈ Ioc 0 N, (majorant t - Λ) n) = _
    rw [majorant_excess]
  rw [he]
  have hh := sum_convolution_mangoldt_le (excessAF t) (excessAF_nonneg ht) N
  rw [reciprocal_excess hN] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (sub_le_sub_right (harmonic_mass_bound hN ht) 1) (by positivity))

lemma smooth_error_le_majorant_excess {t : ℝ} (ht : 0 < t) (n : ℕ) :
    |smoothMangoldt t n - Λ n| ≤ (majorant t n - Λ n) + t*Λ n*Real.log n := by
  have hpos := sub_nonneg.mpr (mangoldt_le_majorant ht.le n)
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, he⟩ := (isPrimePow_nat_iff n).mp hn
    have hn1 := hn.ne_one
    have he' : |smoothMangoldt t n - Λ n| ≤ t*Λ n*Real.log n := by
      subst n
      rw [smoothMangoldt, expDivisorSum_at_zero, one_apply, if_neg hn1, sub_zero,
        expDivisorSum_prime_pow t hp hk, vonMangoldt_apply_pow hk.ne', vonMangoldt_apply_prime hp]
      have hh := exp_slope_error ht (Real.log_natCast_nonneg p)
      have hlog : Real.log p ≤ Real.log (p^k : ℕ) := Real.log_le_log
        (Nat.cast_pos.mpr hp.pos) (Nat.cast_le.mpr (Nat.le_pow hk))
      have hm := mul_le_mul_of_nonneg_left hlog
        (mul_nonneg ht.le (Real.log_natCast_nonneg p))
      exact hh.trans (by nlinarith only [hm])
    linarith
  · rw [vonMangoldt_eq_zero_iff.mpr hn]
    simpa only [sub_zero, mul_zero, zero_mul, add_zero,
      abs_of_nonneg (smoothMangoldt_nonneg ht n)] using smooth_le_majorant ht n

/-- One power of log N suffices for normalized L1 approximation.
This is not a weighted two-variable correlation estimate. -/
theorem joint_l1_bound {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t) :
    (∑ n ∈ Ioc 0 N, |smoothMangoldt t n - Λ n|) ≤
      7*N*(Real.exp (14*(t*(1+Real.log N)))-1+t*(1+Real.log N)) := by
  have hfirst := sum_le_sum (fun n (hn : n ∈ Ioc 0 N) => smooth_error_le_majorant_excess ht n)
  rw [sum_add_distrib] at hfirst
  have hsecond : (∑ n ∈ Ioc 0 N, t*Λ n*Real.log n) ≤ 7*N*(t*(1+Real.log N)) := by
    calc
      _ ≤ ∑ n ∈ Ioc 0 N, t*Λ n*(1+Real.log N) := by
        apply sum_le_sum
        intro n hn
        have hlog := Erdos972PrimePowerError.log_input_le hn
        exact mul_le_mul_of_nonneg_left (by linarith : Real.log n ≤ 1+Real.log N)
          (mul_nonneg ht.le vonMangoldt_nonneg)
      _ = (t*(1+Real.log N))*Chebyshev.psi N := by
        simp only [Chebyshev.psi, Nat.floor_natCast, mul_sum]
        apply sum_congr rfl
        intro n hn
        ring
      _ ≤ (t*(1+Real.log N))*(7*N) := mul_le_mul_of_nonneg_left
        (psi_le_seven_mul (Nat.cast_nonneg N))
        (mul_nonneg ht.le (by positivity [Real.log_natCast_nonneg N]))
      _ = _ := by ring
  have hthird := majorant_excess_sum_bound hN ht.le
  have he : 14*(1+Real.log N)*t = 14*(t*(1+Real.log N)) := by ring
  rw [he] at hthird
  linarith

theorem joint_l1_tendsto (t : ℕ → ℝ)
    (ht : ∀ᶠ N in atTop, 0 < t N)
    (hsmall : Tendsto (fun N => t N*(1+Real.log N)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Ioc 0 N, |smoothMangoldt (t N) n - Λ n|)/(N : ℝ)) atTop (𝓝 0) := by
  have he := (Real.continuous_exp.tendsto (14*0)).comp (hsmall.const_mul 14)
  simp only [mul_zero, Function.comp_def, Real.exp_zero] at he
  have hb := ((he.sub_const 1).add hsmall).const_mul 7
  simp only [sub_self, zero_add, mul_zero] at hb
  apply squeeze_zero' (Eventually.of_forall (fun N => by positivity)) _ hb
  filter_upwards [ht, eventually_ge_atTop (1 : ℕ)] with N ht hN
  apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
  exact (joint_l1_bound hN ht).trans_eq (by ring)

/-- Even in this larger one-variable comparison regime, the damping factor
at D<=N tends to one, not zero. No actual signed-tail lower bound is claimed. -/
theorem joint_l1_regime_damping (t : ℕ → ℝ) (D : ℕ → ℕ)
    (ht : ∀ᶠ N in atTop, 0 < t N)
    (hD : ∀ᶠ N in atTop, D N ≤ N)
    (hsmall : Tendsto (fun N => t N*(1+Real.log N)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => Real.exp (-(t N)*Real.log (D N))) atTop (𝓝 1) := by
  have hz : Tendsto (fun N : ℕ => t N*Real.log (D N)) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hsmall
    · filter_upwards [ht] with N ht
      exact mul_nonneg ht.le (Real.log_natCast_nonneg _)
    · filter_upwards [ht, hD] with N ht hD
      have hd : Real.log (D N) ≤ 1+Real.log N := by
        by_cases hd0 : D N = 0
        · simp only [hd0, Nat.cast_zero, Real.log_zero]
          positivity [Real.log_natCast_nonneg N]
        · have hh := Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd0))
            (Nat.cast_le.mpr hD)
          linarith
      exact mul_le_mul_of_nonneg_left hd ht.le
  have he := (Real.continuous_exp.tendsto (-0)).comp hz.neg
  simpa only [Function.comp_def, neg_zero, Real.exp_zero, neg_mul] using he

#print axioms harmonic_mass_bound
#print axioms majorant_excess_sum_bound
#print axioms joint_l1_bound
#print axioms joint_l1_tendsto
#print axioms joint_l1_regime_damping
end Erdos972JointSmoothL1
