import Submission.PrimeWinnerLogPowerCofactor

/-! A cofactor range larger than every fixed subquadratic power of log N.
This is still a boundary estimate and leaves the interior prime groups open. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma one_add_log_rpow_div_rpow_tendsto_zero (r s : ℝ) (hr : 0 ≤ r) (hs : 0 < s) :
    Tendsto (fun x : ℝ => (1+Real.log x)^r/x^s) atTop (nhds 0) := by
  have ht := (isLittleO_log_rpow_rpow_atTop r hs).tendsto_div_nhds_zero.const_mul
    ((2 : ℝ)^r)
  simp only [mul_zero] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact div_nonneg (Real.rpow_nonneg (by have := Real.log_nonneg hx; positivity) _)
      (Real.rpow_nonneg (by linarith) _)
  · filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,
      eventually_gt_atTop (0 : ℝ)] with x hx hx0
    have hh := Real.rpow_le_rpow (by linarith : 0 ≤ 1+Real.log x)
      (by linarith : 1+Real.log x ≤ 2*Real.log x) hr
    rw [Real.mul_rpow (by norm_num) (by linarith)] at hh
    convert div_le_div_of_nonneg_right hh (Real.rpow_nonneg hx0.le s) using 1
    ring

noncomputable def criticalCofactorWeight (r : ℝ) (N : ℕ) : ℝ :=
  (Real.log N)^2/(1+Real.log (Real.log N))^r

noncomputable def criticalCofactorCutoff (r : ℝ) (N : ℕ) : ℕ :=
  ⌊criticalCofactorWeight r N⌋₊

lemma criticalCofactor_data (r : ℝ) (hr : 0 ≤ r) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ Real.log N ∧
      Real.log N ≤ criticalCofactorWeight r N ∧
      criticalCofactorWeight r N ≤ (Real.log N)^2 ∧
      0 < criticalCofactorCutoff r N ∧
      criticalCofactorCutoff r N ≤ logPowerCofactorCutoff 2 N := by
  have hL : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht := (one_add_log_rpow_div_rpow_tendsto_zero r 1 hr (by norm_num)).comp hL
  simp only [Real.rpow_one,Function.comp_def] at ht
  filter_upwards [hL.eventually_ge_atTop 1,ht.eventually_le_const (by norm_num : (0 : ℝ) < 1)]
    with N hLN hsmall
  have hL0 : 0 < Real.log N := by linarith
  have hb : 1 ≤ 1+Real.log (Real.log N) := by have := Real.log_nonneg hLN; linarith
  have hd := Real.one_le_rpow hb hr
  have hd0 : 0 < (1+Real.log (Real.log N))^r := by linarith
  have hden : (1+Real.log (Real.log N))^r ≤ Real.log N := by
    have hh := (div_le_iff₀ hL0).mp hsmall
    linarith
  have hwlow : Real.log N ≤ criticalCofactorWeight r N := by
    apply (le_div_iff₀ hd0).mpr
    have hh := mul_le_mul_of_nonneg_left hden hL0.le
    nlinarith
  have hwup : criticalCofactorWeight r N ≤ (Real.log N)^2 := by
    apply (div_le_iff₀ hd0).mpr
    have hh := mul_le_mul_of_nonneg_left hd (sq_nonneg (Real.log N))
    nlinarith
  have hK0 : 0 < criticalCofactorCutoff r N :=
    (Nat.one_le_floor_iff _).mpr (hLN.trans hwlow)
  refine ⟨hLN,hwlow,hwup,hK0,?_⟩
  unfold criticalCofactorCutoff logPowerCofactorCutoff
  apply Nat.floor_mono
  simpa only [Real.rpow_two] using hwup

lemma criticalCofactorCutoff_tendsto_atTop (r : ℝ) (hr : 0 ≤ r) :
    Tendsto (criticalCofactorCutoff r) atTop atTop := by
  have hL : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hW : Tendsto (criticalCofactorWeight r) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [criticalCofactor_data r hr,hL.eventually_ge_atTop b] with N hd hN
    exact hN.trans hd.2.1
  exact tendsto_nat_floor_atTop.comp hW

/-- The new real cofactor weight eventually exceeds every constant multiple
of every fixed power (log N)^a with a<2. -/
lemma criticalCofactorWeight_dominates_logPower (r a M : ℝ)
    (hr : 0 ≤ r) (ha : a < 2) :
    ∀ᶠ N : ℕ in atTop, M*(Real.log N)^a ≤ criticalCofactorWeight r N := by
  have hL : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht := ((one_add_log_rpow_div_rpow_tendsto_zero r (2-a) hr
    (by linarith)).comp hL).const_mul M
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    hL.eventually_ge_atTop 1] with N hN hLN
  have hL0 : 0 < Real.log N := by linarith
  have hb0 : 0 < 1+Real.log (Real.log N) := by
    have := Real.log_nonneg hLN
    positivity
  have hden0 : 0 < (1+Real.log (Real.log N))^r := Real.rpow_pos_of_pos hb0 r
  have hpow0 : 0 < (Real.log N)^(2-a) := Real.rpow_pos_of_pos hL0 _
  have hh : M*(1+Real.log (Real.log N))^r ≤ (Real.log N)^(2-a) := by
    have hh' : (M*(1+Real.log (Real.log N))^r)/(Real.log N)^(2-a) ≤ 1 := by
      simpa only [mul_div_assoc,Function.comp_apply] using hN
    simpa only [one_mul] using (div_le_iff₀ hpow0).mp hh'
  have hm := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hL0.le a)
  rw [← Real.rpow_add hL0,sub_add_cancel,Real.rpow_two] at hm
  unfold criticalCofactorWeight
  apply (le_div_iff₀ hden0).mpr
  nlinarith

lemma logPowerCofactorCutoff_le_critical_eventually (r a : ℝ)
    (hr : 0 ≤ r) (ha : a < 2) :
    ∀ᶠ N : ℕ in atTop, logPowerCofactorCutoff a N ≤ criticalCofactorCutoff r N := by
  filter_upwards [criticalCofactorWeight_dominates_logPower r a 1 hr ha]
    with N hN
  apply Nat.floor_mono
  simpa only [one_mul] using hN

lemma criticalCofactor_main_term_bound (r : ℝ) (N : ℕ) (hL : 1 ≤ Real.log N) :
    criticalCofactorWeight r N * (logPowerCofactorExponent 2 N+1/Real.log N)^2 ≤
      (Real.log 2+3)^2/(1+Real.log (Real.log N))^(r-2) := by
  have hL0 : 0 < Real.log N := by linarith
  have ht0 := Real.log_nonneg hL
  have hb0 : 0 < 1+Real.log (Real.log N) := by positivity
  have h2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have ha : 0 ≤ Real.log 2+2*Real.log (Real.log N)+1 := by positivity
  have hab : Real.log 2+2*Real.log (Real.log N)+1 ≤
      (Real.log 2+3)*(1+Real.log (Real.log N)) := by nlinarith
  have he : logPowerCofactorExponent 2 N+1/Real.log N =
      (Real.log 2+2*Real.log (Real.log N)+1)/Real.log N := by
    unfold logPowerCofactorExponent
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (Real.rpow_pos_of_pos hL0 2).ne', Real.log_rpow hL0]
    ring
  rw [he,criticalCofactorWeight]
  have he' : (Real.log N)^2/(1+Real.log (Real.log N))^r *
      ((Real.log 2+2*Real.log (Real.log N)+1)/Real.log N)^2 =
      (Real.log 2+2*Real.log (Real.log N)+1)^2/(1+Real.log (Real.log N))^r := by
    field_simp
  rw [he']
  have hs := div_le_div_of_nonneg_right (pow_le_pow_left₀ ha hab 2)
    (Real.rpow_nonneg hb0.le r)
  apply hs.trans_eq
  rw [mul_pow,Real.rpow_sub hb0,Real.rpow_two]
  field_simp

/-- For every fixed r>2, energy above the cutoff
N / floor((log N)^2 / (1+log log N)^r) is o(N). -/
theorem primeWinnerEnergyAbove_critical_cofactor_tendsto (r : ℝ) (hr : 2 < r) :
    Tendsto (fun N : ℕ =>
      primeWinnerEnergyAbove (N/criticalCofactorCutoff r N) N / N)
      atTop (nhds 0) := by
  have hr0 : 0 ≤ r := by linarith
  have hL : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLL : Tendsto (fun N : ℕ => 1+Real.log (Real.log N)) atTop atTop :=
    tendsto_const_nhds.add_atTop (Real.tendsto_log_atTop.comp hL)
  have hmain := (tendsto_const_nhds.div_atTop
    ((tendsto_rpow_atTop (by linarith : 0 < r-2)).comp hLL) :
      Tendsto (fun N : ℕ => (Real.log 2+3)^2/(1+Real.log (Real.log N))^(r-2))
        atTop (nhds 0)).const_mul (3*largePairConstant)
  have herr := (log_nat_pow_div_rpow_tendsto_zero 2 (1/2) (by norm_num)).const_mul
    (3*(2 : ℝ)^65)
  have hend : Tendsto (fun N : ℕ => 3*(Real.log N)^2/N) atTop (nhds 0) := by
    simpa only [Real.rpow_one,mul_div_assoc,mul_zero] using
      (log_nat_pow_div_rpow_tendsto_zero 2 1 (by norm_num)).const_mul 3
  have ht := (hmain.add herr).add hend
  simp only [mul_zero,add_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun _ => by
    unfold primeWinnerEnergyAbove; positivity)) _ ht
  filter_upwards [criticalCofactor_data r hr0,logPowerCofactor_cutoff_data 2 (by norm_num),
    eventually_gt_atTop (1 : ℕ)] with N hd hpow hN
  obtain ⟨hLN,hwlow,hwup,hK0,hKK⟩ := hd
  obtain ⟨_,_,hu0,hu,hcut⟩ := hpow
  let K := criticalCofactorCutoff r N
  let W := criticalCofactorWeight r N
  let u := logPowerCofactorExponent 2 N
  have hW : 1 ≤ W := hLN.trans hwlow
  have hKle : (K : ℝ) ≤ W := Nat.floor_le (by linarith)
  have hcoef : (2*K+1 : ℝ) ≤ 3*W := by linarith
  have hcut' : (N : ℝ)^(1-u) ≤ ((N/K : ℕ) : ℝ) :=
    hcut.trans (by exact_mod_cast Nat.div_le_div_left hKK hK0)
  have hsize : N ≤ K*(N/K+1) := by
    have hh := Nat.mod_lt N hK0
    have he := Nat.mod_add_div N K
    nlinarith
  have hb := primeWinnerEnergyAbove_top_ratio_bound (N/K) K N u hN hu0 hu hcut' hsize
  have hC : 0 ≤ largePairConstant := by unfold largePairConstant; positivity
  have hcoef' := mul_le_mul_of_nonneg_right hcoef (show 0 ≤
    largePairConstant*(u+1/Real.log N)^2+(2 : ℝ)^65*(N : ℝ)^(-1/2 : ℝ)+1/N by positivity)
  have hm := mul_le_mul_of_nonneg_left (criticalCofactor_main_term_bound r N hLN)
    (show 0 ≤ 3*largePairConstant by positivity)
  have hexp : (N : ℝ)^(-1/2 : ℝ) = 1/(N : ℝ)^(1/2 : ℝ) := by
    rw [show (-1/2 : ℝ) = -(1/2) by ring,Real.rpow_neg (Nat.cast_nonneg N)]
    exact (one_div _).symm
  have he := mul_le_mul_of_nonneg_left hwup
    (show 0 ≤ 3*(2 : ℝ)^65*(N : ℝ)^(-1/2 : ℝ) by positivity)
  have he' := mul_le_mul_of_nonneg_left hwup
    (show 0 ≤ 3/(N : ℝ) by positivity)
  change 3*largePairConstant*(W*(u+1/Real.log N)^2) ≤ _ at hm
  change 3*(2 : ℝ)^65*(N : ℝ)^(-1/2 : ℝ)*W ≤ _ at he
  change 3/(N : ℝ)*W ≤ _ at he'
  have hsum := add_le_add (add_le_add hm he) he'
  apply (hb.trans hcoef').trans
  convert hsum using 1 <;> rw [hexp] <;> ring

#print axioms criticalCofactor_data
#print axioms criticalCofactorWeight_dominates_logPower
#print axioms criticalCofactorCutoff_tendsto_atTop
#print axioms primeWinnerEnergyAbove_critical_cofactor_tendsto
end Erdos371
