import Submission.LogCriticalExposureBudget

/-! Unconditional void estimates with the critical power and a fixed
logarithmic loss. These do not exclude a single exceptional phase, so they
do not settle the quadratic Jacobsthal conjecture. -/
namespace Erdos970.GapAverages
open Finset Real Filter
set_option maxHeartbeats 2000000

lemma eventually_log_exposure_core_cost (D b : ℕ) :
    ∀ᶠ t : ℕ in atTop,
      ((D : ℝ)+2)*(t : ℝ)^30*(3+40*log t) ≤ (logExposureSize b t : ℝ)/400 := by
  let ε : ℝ := 1/(34400*((D : ℝ)+2))
  have hε : 0 < ε := by dsimp [ε]; positivity
  filter_upwards [eventually_nat_log_power_small (b+1) 10 (by omega) ε hε,
    eventually_nat_log_power_small b 40 (by omega) (1/2) (by norm_num),
    eventually_log_nat_ge 1,eventually_ge_atTop 1] with t hs hsmall hL ht
  have hL0 : 0 < log (t : ℝ) := by linarith only [hL]
  have hpow : 0 < log (t : ℝ)^b := pow_pos hL0 _
  have hh := logExposureSize_bounds b t ht hL (by linarith only [hsmall])
  have hbase : ((D : ℝ)+2)*43*log (t : ℝ)^(b+1) ≤ (t : ℝ)^10/800 := by
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ ((D : ℝ)+2)*43 by positivity)
    apply hm.trans_eq
    dsimp only [ε]
    field_simp
    <;> ring
  have hm := mul_le_mul_of_nonneg_right hbase (show 0 ≤ (t : ℝ)^30 by positivity)
  have hm' : ((D : ℝ)+2)*(t : ℝ)^30*(43*log (t : ℝ))*log (t : ℝ)^b ≤
      (t : ℝ)^40/800 := by
    convert hm using 1 <;> ring
  have hcoef : 3+40*log (t : ℝ) ≤ 43*log (t : ℝ) := by linarith only [hL]
  have he := mul_le_mul_of_nonneg_left hcoef
    (show 0 ≤ ((D : ℝ)+2)*(t : ℝ)^30 by positivity)
  have he' := mul_le_mul_of_nonneg_right he hpow.le
  have hfin : ((D : ℝ)+2)*(t : ℝ)^30*(3+40*log t) ≤
      (t : ℝ)^40/(800*log (t : ℝ)^b) := by
    apply (le_div_iff₀ (by positivity : 0 < 800*log (t : ℝ)^b)).mpr
    have hh := he'.trans hm'
    nlinarith only [hh]
  apply hfin.trans
  have hlo := mul_le_mul_of_nonneg_right hh.2.2.2 (by norm_num : (0 : ℝ) ≤ 1/400)
  convert hlo using 1 <;> ring

lemma variable_exposure_core_envelope (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hSP : S ⊆ P)
    (k t D j : ℕ) (ht : 0 < t) (hj : 0 < j)
    (hjt : (j : ℝ) ≤ (t : ℝ)^40)
    (hScard : S.card ≤ D*t^30+1)
    (htail : (∑ p ∈ P \ S, (p : ℝ)⁻¹) ≤ 199/200)
    (hcost : ((D : ℝ)+2)*(t : ℝ)^30*(3+40*log t) ≤ (j : ℝ)/400)
    (hb : IsJacobsthalBound (j-1) k) :
    coveredFraction P k ≤ exp (-(j : ℝ)/400) := by
  have hh := coveredFraction_le_general_core P S hP hSP k j hj
    hb (199/200) (by norm_num) htail
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hlog : 0 ≤ log (t : ℝ) := log_nonneg ht1
  have hpow : (1 : ℝ) ≤ (t : ℝ)^40 := one_le_pow₀ ht1
  have hsmall : log (1+(j : ℝ)/(199/200)) ≤ 3+40*log (t : ℝ) := by
    have hl := log_le_log (by positivity : (0 : ℝ) < 1+(j : ℝ)/(199/200))
      (show 1+(j : ℝ)/(199/200) ≤ 3*(t : ℝ)^40 by nlinarith only [hjt,hpow])
    rw [log_mul (by norm_num : (3 : ℝ) ≠ 0) (pow_ne_zero _ ht0.ne'),log_pow] at hl
    have h3 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num only [Nat.cast_ofNat] at hl
    linarith only [hl,h3]
  have hlogj : log (j : ℝ) ≤ 40*log (t : ℝ) := by
    have hh := log_le_log hj0 hjt
    simpa only [log_pow,Nat.cast_ofNat] using hh
  have hcount : (S.card : ℝ)+1 ≤ ((D : ℝ)+2)*(t : ℝ)^30 := by
    have hc : (S.card : ℝ) ≤ (D : ℝ)*(t : ℝ)^30+1 := by exact_mod_cast hScard
    have ht30 : (1 : ℝ) ≤ (t : ℝ)^30 := one_le_pow₀ ht1
    nlinarith only [hc,ht30]
  have hover : (S.card : ℝ)*log (1+(j : ℝ)/(199/200))+1+log (j : ℝ)/2 ≤
      (j : ℝ)/400 := by
    have h1 := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg S.card)
    have h2 := mul_le_mul_of_nonneg_right hcount
      (show 0 ≤ 3+40*log (t : ℝ) by positivity)
    nlinarith only [h1,h2,hcost,hlogj,hlog]
  have hmain : log (199/200 : ℝ) ≤ -1/200 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 199/200)
    linarith only [h]
  have hneg := mul_le_mul_of_nonneg_left hmain hj0.le
  exact hh.trans (exp_le_exp.mpr (by linarith only [hover,hneg]))

lemma log_exposure_core_envelope (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k t D b : ℕ) (ht : 0 < t) (hL : 1 ≤ log (t : ℝ))
    (hsmall : log (t : ℝ)^b ≤ (t : ℝ)^40/2)
    (hcard : P.card ≤ t^80) (hD : 1024 ≤ D)
    (hlogD : 2048*(WeightedMertens.boundConstant+1) ≤ log (D : ℝ))
    (hcost : ((D : ℝ)+2)*(t : ℝ)^30*(3+40*log t) ≤ (logExposureSize b t : ℝ)/400)
    (hb : IsJacobsthalBound (logExposureSize b t-1) k) :
    coveredFraction P k ≤ exp (-(t : ℝ)^40/(800*log (t : ℝ)^b)) := by
  let S := P.filter (fun p => p ≤ D*t^30)
  have hSP : S ⊆ P := filter_subset _ _
  have hScard : S.card ≤ D*t^30+1 := by
    have hs : S ⊆ range (D*t^30+1) := by
      intro p hp
      exact mem_range.mpr (by have := (mem_filter.mp hp).2; omega)
    simpa only [card_range] using card_le_card hs
  have htail : (∑ p ∈ P \ S, (p : ℝ)⁻¹) ≤ 199/200 := by
    have he : P \ S = P.filter (fun p => D*t^30 < p) := by
      ext p
      simp only [S,mem_filter]
      by_cases hp : p ∈ P <;> simp [hp]
    rw [he]
    simpa only [one_div] using WeightedMertens.tail_three_eighths P hP t D ht hD hlogD hcard
  have hsize := logExposureSize_bounds b t ht hL hsmall
  have hh := variable_exposure_core_envelope P S hP hSP k t D (logExposureSize b t)
    ht hsize.1 hsize.2.1 hScard htail hcost hb
  apply hh.trans
  apply exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_right hsize.2.2.2 (by norm_num : (0 : ℝ) ≤ 1/400)
  have he : (t : ℝ)^40/(2*log (t : ℝ)^b)*(1/400) =
      (t : ℝ)^40/(800*log (t : ℝ)^b) := by ring
  rw [he] at hm
  convert neg_le_neg hm using 1 <;> ring

/-- A single fixed logarithmic loss permits the critical square-root power
in an unconditional, prime-set-uniform linear-length void estimate. -/
theorem exists_log_critical_linear_void : ∃ b : ℕ, 0 < b ∧
    ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      coveredFraction P k ≤ exp (-sqrt (k : ℝ)/(800*log (k : ℝ)^b)) := by
  obtain ⟨b,hb,hbudget⟩ := exists_log_exposure_budget
  let D := FiniteSelberg.thirteenSixteenthCutoffScale
  have hD : 1024 ≤ D := (by norm_num : 1024 ≤ 65536).trans
    FiniteSelberg.thirteenSixteenthCutoffScale_ge
  have hlogD : 2048*(WeightedMertens.boundConstant+1) ≤ log (D : ℝ) := exposureCutoffScale_log
  have hready := hbudget.and ((eventually_log_exposure_core_cost D b).and
    ((eventually_log_nat_ge 1).and
      (eventually_nat_log_power_small b 40 (by omega) (1/2) (by norm_num))))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hready
  let T := max N 2
  have hT : 0 < T := by dsimp [T]; omega
  refine ⟨b,hb,?_⟩
  filter_upwards [eventually_ge_atTop (T^80)] with k hk
  intro P hP hPk
  have hkpos : 0 < k := (Nat.pow_pos hT).trans_le hk
  obtain ⟨t,ht,hkt,hroot,htk⟩ := SoftExposure.exists_power_envelope k 80 hkpos (by omega)
  have hTt : T ≤ t := (Nat.pow_le_pow_iff_left (by norm_num : (80 : ℕ) ≠ 0)).mp (hk.trans hkt)
  have hNt : N ≤ t := (le_max_left _ _).trans hTt
  obtain ⟨hbudget,hcost,hL,hsmall⟩ := hN t hNt
  have hh := log_exposure_core_envelope P hP k t D b ht hL (by linarith only [hsmall])
    (hPk.trans hkt) hD hlogD hcost (hbudget.2 k hroot)
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hL0 : 0 < log (t : ℝ) := by linarith only [hL]
  have hlogtk : log (t : ℝ) ≤ log (k : ℝ) := log_le_log ht0 (by exact_mod_cast htk)
  have hden : log (t : ℝ)^b ≤ log (k : ℝ)^b := pow_le_pow_left₀ hL0.le hlogtk b
  have hnum : sqrt (k : ℝ) ≤ (t : ℝ)^40 := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hh : (k : ℝ) ≤ (t : ℝ)^80 := by exact_mod_cast hkt
    convert hh using 1 <;> ring
  have hquot : sqrt (k : ℝ)/(800*log (k : ℝ)^b) ≤
      (t : ℝ)^40/(800*log (t : ℝ)^b) := by
    apply le_trans (div_le_div_of_nonneg_left (sqrt_nonneg _)
      (by positivity : 0 < 800*log (t : ℝ)^b)
      (mul_le_mul_of_nonneg_left hden (by norm_num)))
    exact div_le_div_of_nonneg_right hnum (by positivity)
  apply hh.trans
  apply exp_le_exp.mpr
  simpa only [neg_div] using neg_le_neg hquot

/-- Quadratic-length version of the same unconditional estimate. The loss
is still logarithmic, and the phase-entropy threshold is not reached. -/
theorem exists_log_critical_quadratic_void : ∃ b : ℕ, 0 < b ∧
    ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      coveredFraction P (k^2) ≤ exp (-(k : ℝ)/(800*2^b*log (k : ℝ)^b)) := by
  obtain ⟨b,hb,hlinear⟩ := exists_log_critical_linear_void
  refine ⟨b,hb,?_⟩
  have he := (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).eventually hlinear
  filter_upwards [he] with k hk
  intro P hP hPk
  have hh := hk P hP (hPk.trans (Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0) k))
  simpa only [Nat.cast_pow,sqrt_sq (Nat.cast_nonneg k),log_pow,Nat.cast_ofNat,
    mul_pow,mul_assoc] using hh

/-- Even an arbitrary fixed positive multiplier of the new rate remains
strictly below the phase-entropy rate. This compares the two envelopes;
it does not assert any positive lower bound for the actual void fraction. -/
theorem eventually_log_critical_envelope_above_entropy (A : ℝ) (hA : 0 < A) (b : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      exp (-(k : ℝ)*log ((k : ℝ)+2)) <
        exp (-A*(k : ℝ)/log (k : ℝ)^b) := by
  filter_upwards [eventually_log_nat_ge 1,eventually_log_nat_ge (A+1),
    eventually_ge_atTop 1] with k hL hAlog hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hL0 : 0 < log (k : ℝ) := by linarith only [hL]
  have hpow : (1 : ℝ) ≤ log (k : ℝ)^b := one_le_pow₀ hL
  have hquot : A*(k : ℝ)/log (k : ℝ)^b ≤ A*(k : ℝ) :=
    div_le_self (by positivity) hpow
  have hlog : A < log ((k : ℝ)+2) := by
    have hh := log_le_log hk0 (show (k : ℝ) ≤ (k : ℝ)+2 by linarith)
    linarith only [hh,hAlog]
  have hm := mul_lt_mul_of_pos_left hlog hk0
  apply exp_lt_exp.mpr
  simp only [neg_div,neg_mul]
  nlinarith only [hm,hquot]

#print axioms eventually_log_critical_envelope_above_entropy
#print axioms exists_log_critical_linear_void
#print axioms exists_log_critical_quadratic_void
end Erdos970.GapAverages
