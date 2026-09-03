import Submission.PrimeWinnerGrowingCofactor

/-! Sublinear energy above N/(log N)^a for every fixed 0<=a<2.
These are exponent-one boundary cutoffs, not fixed-interior power cutoffs. -/

namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

noncomputable def logPowerCofactorCutoff (a : ℝ) (N : ℕ) : ℕ :=
  ⌊(Real.log N)^a⌋₊

noncomputable def logPowerCofactorExponent (a : ℝ) (N : ℕ) : ℝ :=
  Real.log (2*(Real.log N)^a)/Real.log N

lemma logPowerCofactorCutoff_tendsto_atTop (a : ℝ) (ha : 0 < a) :
    Tendsto (logPowerCofactorCutoff a) atTop atTop :=
  tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop ha).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

lemma logPowerCofactorExponent_tendsto_zero (a : ℝ) :
    Tendsto (logPowerCofactorExponent a) atTop (nhds 0) := by
  have hL : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun N : ℕ => Real.log 2/Real.log N) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hL
  have h2 : Tendsto (fun N : ℕ => Real.log (Real.log N)/Real.log N)
      atTop (nhds 0) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.comp hL
  have ht := h1.add (h2.const_mul a)
  simp only [mul_zero,add_zero] at ht
  apply ht.congr'
  filter_upwards [hL.eventually_gt_atTop 0] with N hN
  dsimp only [logPowerCofactorExponent]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (Real.rpow_pos_of_pos hN a).ne', Real.log_rpow hN]
  ring

lemma logPowerCofactor_cutoff_data (a : ℝ) (ha : 0 ≤ a) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ Real.log N ∧
      0 < logPowerCofactorCutoff a N ∧
      0 ≤ logPowerCofactorExponent a N ∧
      logPowerCofactorExponent a N ≤ 1/8 ∧
      (N : ℝ)^(1-logPowerCofactorExponent a N) ≤
        ((N/logPowerCofactorCutoff a N : ℕ) : ℝ) := by
  have hL : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hL.eventually_ge_atTop 1,
    (logPowerCofactorExponent_tendsto_zero a).eventually_le_const
      (by norm_num : (0 : ℝ) < 1/8), eventually_gt_atTop (1 : ℕ)]
    with N hL hu hN
  have hL0 : 0 < Real.log N := by linarith
  have hW : 1 ≤ (Real.log N)^a := Real.one_le_rpow hL ha
  have hK : 0 < logPowerCofactorCutoff a N := (Nat.one_le_floor_iff _).mpr hW
  have hKle : (logPowerCofactorCutoff a N : ℝ) ≤ (Real.log N)^a :=
    Nat.floor_le (by positivity)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hpos : 0 ≤ logPowerCofactorExponent a N :=
    div_nonneg (Real.log_nonneg (by linarith)) hL0.le
  have hpow : (N : ℝ)^(logPowerCofactorExponent a N) = 2*(Real.log N)^a := by
    rw [Real.rpow_def_of_pos hN0]
    unfold logPowerCofactorExponent
    rw [mul_div_cancel₀ _ hL0.ne']
    exact Real.exp_log (by positivity)
  have hKN : logPowerCofactorCutoff a N ≤ N := by
    have hp : (N : ℝ)^(logPowerCofactorExponent a N) ≤ N := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hN1 (show logPowerCofactorExponent a N ≤ 1 by linarith)
    rw [hpow] at hp
    have hh : (logPowerCofactorCutoff a N : ℝ) ≤ N := by linarith
    exact_mod_cast hh
  refine ⟨hL,hK,hpos,hu,?_⟩
  apply div_cutoff_ge_power_of_mul_le_rpow _ _ _ hK hKN
  rw [hpow]
  linarith

lemma affine_log_square_div_rpow_tendsto_zero (a r : ℝ) (hr : 0 < r) :
    Tendsto (fun x : ℝ => (Real.log 2+a*Real.log x+1)^2/x^r)
      atTop (nhds 0) := by
  have h0 : Tendsto (fun x : ℝ => 1/x^r) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop hr)
  have h1 : Tendsto (fun x : ℝ => Real.log x/x^r) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero
  have h2 : Tendsto (fun x : ℝ => (Real.log x)^2/x^r) atTop (nhds 0) := by
    simpa only [Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hr).tendsto_div_nhds_zero
  have ht := ((h0.const_mul ((Real.log 2+1)^2)).add
    (h1.const_mul (2*(Real.log 2+1)*a))).add (h2.const_mul (a^2))
  simp only [mul_zero,add_zero] at ht
  convert ht using 1
  ext x
  ring

lemma log_nat_rpow_div_rpow_tendsto_zero (a r : ℝ) (hr : 0 < r) :
    Tendsto (fun N : ℕ => (Real.log N)^a/(N : ℝ)^r) atTop (nhds 0) :=
  (isLittleO_log_rpow_rpow_atTop a hr).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop

/-- The energy of winner groups with cofactor at most a subquadratic fixed
power of log N is o(N). The complementary groups remain uncontrolled. -/
theorem primeWinnerEnergyAbove_logPower_cofactor_tendsto (a : ℝ)
    (ha : 0 ≤ a) (ha2 : a < 2) :
    Tendsto (fun N : ℕ =>
      primeWinnerEnergyAbove (N/logPowerCofactorCutoff a N) N / N)
      atTop (nhds 0) := by
  have hL : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmain := ((affine_log_square_div_rpow_tendsto_zero a (2-a)
    (by linarith)).comp hL).const_mul (3*largePairConstant)
  have herr := (log_nat_rpow_div_rpow_tendsto_zero a (1/2) (by norm_num)).const_mul
    (3*(2 : ℝ)^65)
  have hend : Tendsto (fun N : ℕ => 3*(Real.log N)^a/N) atTop (nhds 0) := by
    simpa only [Real.rpow_one,mul_div_assoc,mul_zero] using
      (log_nat_rpow_div_rpow_tendsto_zero a 1 (by norm_num)).const_mul 3
  have ht := (hmain.add herr).add hend
  simp only [mul_zero,add_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun _ => by
    unfold primeWinnerEnergyAbove; positivity)) _ ht
  filter_upwards [logPowerCofactor_cutoff_data a ha, eventually_gt_atTop (1 : ℕ)]
    with N hdata hN
  obtain ⟨hL,hK,hupos,hu,hcut⟩ := hdata
  let K := logPowerCofactorCutoff a N
  let u := logPowerCofactorExponent a N
  have hL0 : 0 < Real.log N := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hW : 1 ≤ (Real.log N)^a := Real.one_le_rpow hL ha
  have hsize : N ≤ K*(N/K+1) := by
    have hh := Nat.mod_lt N hK
    have he := Nat.mod_add_div N K
    nlinarith
  have hcoef : (2*K+1 : ℝ) ≤ 3*(Real.log N)^a := by
    have hk : (K : ℝ) ≤ (Real.log N)^a := Nat.floor_le (by positivity)
    linarith
  have hb := primeWinnerEnergyAbove_top_ratio_bound (N/K) K N u hN hupos hu hcut hsize
  have hC : 0 ≤ largePairConstant := by unfold largePairConstant; positivity
  have hnonneg : 0 ≤ largePairConstant*(u+1/Real.log N)^2 +
      (2 : ℝ)^65*(N : ℝ)^(-1/2 : ℝ)+1/N := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcoef hnonneg
  have hexp : (N : ℝ)^(-1/2 : ℝ) = 1/(N : ℝ)^(1/2 : ℝ) := by
    rw [show (-1/2 : ℝ) = -(1/2) by ring, Real.rpow_neg (Nat.cast_nonneg N)]
    exact (one_div _).symm
  have huform : u = (Real.log 2+a*Real.log (Real.log N))/Real.log N := by
    dsimp only [u,logPowerCofactorExponent]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (Real.rpow_pos_of_pos hL0 a).ne', Real.log_rpow hL0]
  apply (hb.trans hmul).trans_eq
  rw [hexp,huform]
  simp only [Function.comp_apply]
  rw [Real.rpow_sub hL0, Real.rpow_two]
  field_simp

#print axioms logPowerCofactor_cutoff_data
#print axioms affine_log_square_div_rpow_tendsto_zero
#print axioms primeWinnerEnergyAbove_logPower_cofactor_tendsto
end Erdos371
