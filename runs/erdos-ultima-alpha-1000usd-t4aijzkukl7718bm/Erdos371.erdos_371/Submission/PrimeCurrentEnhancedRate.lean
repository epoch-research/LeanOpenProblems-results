import Submission.PrimeCurrentQuantitativeL2

/-! A stronger subpower rate from the large-u smooth-number estimate.
The critical prime-weighted energy and the original density conjecture
remain unproved. -/

namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable def enhancedCurrentScale (N : ℕ) : ℝ :=
  Real.sqrt (Real.log N * Real.log (Real.log N))

noncomputable def enhancedCurrentRateConstant : ℝ :=
  (Real.exp 4*(1+2/Real.log 2))^2+primeCurrentL2TailConstant

lemma enhancedCurrentRateConstant_pos : 0<enhancedCurrentRateConstant := by
  have h := primeCurrentL2TailConstant_nonneg
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  unfold enhancedCurrentRateConstant
  positivity

lemma primeCurrentSquaredError_large_u_scale (N : ℕ) (hN : 0<N)
    (t : ℝ) (ht1 : 1≤t) (ht3 : Real.log 3≤t)
    (hL : 1≤Real.log N) (hlogL : Real.log (Real.log N)≤t)
    (hpow : 1024≤(Real.log N)^(1/4 : ℝ))
    (hsize : 2*t*(Real.log N)^(1/4 : ℝ)≤Real.log N)
    (hscale : t^2=Real.log N*Real.log (Real.log N)) :
    primeCurrentSquaredError N ≤
      enhancedCurrentRateConstant*(1+t)^2*Real.exp (-t/64) := by
  let B : ℕ := ⌈Real.exp t⌉₊
  let L : ℝ := Real.log N
  let u : ℝ := L/Real.log (B+1 : ℝ)
  have ht : 0<t := by linarith
  have hL0 : 0<L := by dsimp [L]; linarith
  have hB : 0<B := Nat.ceil_pos.mpr (Real.exp_pos t)
  have hB0 : (0 : ℝ)<B+1 := by positivity
  have hfloor : Real.exp t≤(B : ℝ) := Nat.le_ceil _
  have hceil : (B : ℝ)<Real.exp t+1 := Nat.ceil_lt_add_one (Real.exp_nonneg t)
  have hlogB : t≤Real.log (B+1 : ℝ) := by
    simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos t) (show Real.exp t≤B+1 by linarith)
  have hlogB0 : 0<Real.log (B+1 : ℝ) := ht.trans_le hlogB
  have hlogBup : Real.log (B+1 : ℝ)≤2*t := by
    have he : 1≤Real.exp t := Real.one_le_exp_iff.mpr ht.le
    calc
      _ ≤ Real.log (3*Real.exp t) := Real.log_le_log hB0 (by linarith)
      _ = Real.log 3+t := by rw [Real.log_mul (by norm_num) (Real.exp_ne_zero t),Real.log_exp]
      _ ≤ _ := by linarith
  have hulo : L/(2*t)≤u := div_le_div_of_nonneg_left hL0.le (by positivity) hlogBup
  have hupow : L^(1/4 : ℝ)≤u := by
    apply le_trans _ hulo
    apply (le_div_iff₀ (by positivity : (0 : ℝ)<2*t)).mpr
    dsimp only [L]
    nlinarith
  have hu : 1024≤u := hpow.trans hupow
  have hu0 : 0<u := by linarith
  have huup : u≤L := by
    apply (div_le_iff₀ hlogB0).mpr
    have hh := mul_le_mul_of_nonneg_left (ht1.trans hlogB) hL0.le
    simpa only [mul_one] using hh
  have hrange : Real.log u≤4*Real.log (B+1 : ℝ) := by
    have hh := Real.log_le_log hu0 huup
    change Real.log L≤t at hlogL
    linarith
  have huscale : u*Real.log (B+1 : ℝ)=Real.log N := div_mul_cancel₀ _ hlogB0.ne'
  have hlogulo : Real.log L/4≤Real.log u := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hL0 _) hupow
    rw [Real.log_rpow hL0] at hh
    linarith
  have hlogL0 : 0≤Real.log L := Real.log_nonneg hL
  have hlarge : t/8≤u*Real.log u := by
    have hh := mul_le_mul hulo hlogulo (by positivity : 0≤Real.log L/4) hu0.le
    have he : L/(2*t)*(Real.log L/4)=t/8 := by
      apply (eq_div_iff (by norm_num : (8 : ℝ)≠0)).mpr
      have ht0 : t≠0 := ht.ne'
      field_simp
      change t^2=L*Real.log L at hscale
      nlinarith
    rw [he] at hh
    exact hh
  have hhead0 := primeCurrentHeadError_large_u_bound B N hB hN u hu huscale hrange
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hcoef : 1+Real.log (B+1 : ℝ)/Real.log 2≤(1+2/Real.log 2)*(1+t) := by
    have hh := div_le_div_of_nonneg_right hlogBup hl2.le
    have hp : 0≤2/Real.log 2 := by positivity
    rw [show 2*t/Real.log 2=(2/Real.log 2)*t by ring] at hh
    nlinarith
  have hhead : primeCurrentHeadError B N ≤
      (Real.exp 4*(1+2/Real.log 2))*(1+t)*Real.exp (-t/128) := by
    apply hhead0.trans
    calc
      _ ≤ (Real.exp 4*((1+2/Real.log 2)*(1+t)))*Real.exp (-t/128) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hcoef (Real.exp_nonneg _)
        · apply Real.exp_le_exp.mpr
          linarith
        · exact Real.exp_nonneg _
        · positivity
      _ = _ := by ring
  have hsquare : (primeCurrentHeadError B N)^2 ≤
      (Real.exp 4*(1+2/Real.log 2))^2*(1+t)^2*Real.exp (-t/64) := by
    have hh := pow_le_pow_left₀ (by unfold primeCurrentHeadError; positivity) hhead 2
    apply hh.trans_eq
    rw [mul_pow,mul_pow,← Real.exp_nat_mul]
    congr 2
    norm_num
    ring
  have htail : (B+1 : ℝ)^(-1/4 : ℝ)≤Real.exp (-t/64) := by
    calc
      _ ≤ (Real.exp t)^(-1/4 : ℝ) := Real.rpow_le_rpow_of_nonpos
        (Real.exp_pos _) (by linarith) (by norm_num)
      _ = Real.exp (-t/4) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hpoly : 1≤(1+t)^2 := by nlinarith
  have htail' : primeCurrentL2TailConstant*(B+1 : ℝ)^(-1/4 : ℝ)≤
      primeCurrentL2TailConstant*(1+t)^2*Real.exp (-t/64) := by
    apply (mul_le_mul_of_nonneg_left htail primeCurrentL2TailConstant_nonneg).trans
    have hh := mul_le_mul_of_nonneg_left hpoly
      (show 0≤primeCurrentL2TailConstant*Real.exp (-t/64) by
        exact mul_nonneg primeCurrentL2TailConstant_nonneg (Real.exp_nonneg _))
    convert hh using 1 <;> ring
  apply (primeCurrentSquaredError_head_tail B N).trans
  apply (add_le_add hsquare htail').trans_eq
  unfold enhancedCurrentRateConstant
  ring

lemma enhancedCurrentScale_tendsto : Tendsto enhancedCurrentScale atTop atTop := by
  have hL : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLL := Real.tendsto_log_atTop.comp hL
  apply tendsto_atTop_mono' atTop _ (Real.tendsto_sqrt_atTop.comp hL)
  filter_upwards [hLL.eventually_ge_atTop 1] with N hN
  unfold enhancedCurrentScale
  apply Real.sqrt_le_sqrt
  exact le_mul_of_one_le_right (Real.log_natCast_nonneg N) hN

lemma sqrt_log_scale_size (L : ℝ) (hL : 1≤L)
    (hlog : Real.log L≤Real.sqrt L/4) :
    2*Real.sqrt (L*Real.log L)*L^(1/4 : ℝ)≤L := by
  have hL0 : 0<L := by linarith
  have hlog0 : 0≤Real.log L := Real.log_nonneg hL
  have hs : (Real.sqrt (L*Real.log L))^2=L*Real.log L :=
    Real.sq_sqrt (mul_nonneg hL0.le hlog0)
  have hz : (L^(1/4 : ℝ))^2=Real.sqrt L := by
    rw [← Real.rpow_mul_natCast hL0.le]
    norm_num
    exact (Real.sqrt_eq_rpow L).symm
  have hsq : (2*Real.sqrt (L*Real.log L)*L^(1/4 : ℝ))^2≤L^2 := by
    rw [mul_pow,mul_pow,hs,hz]
    have hh := mul_le_mul_of_nonneg_right hlog
      (show 0≤4*L*Real.sqrt L by positivity)
    have hroot := Real.sq_sqrt hL0.le
    nlinarith
  have hn : 0≤2*Real.sqrt (L*Real.log L)*L^(1/4 : ℝ) := by positivity
  nlinarith

lemma enhancedCurrentScale_data :
    ∀ᶠ N : ℕ in atTop,
      0<N ∧ 1≤enhancedCurrentScale N ∧ Real.log 3≤enhancedCurrentScale N ∧
      1≤Real.log N ∧ Real.log (Real.log N)≤enhancedCurrentScale N ∧
      1024≤(Real.log N)^(1/4 : ℝ) ∧
      2*enhancedCurrentScale N*(Real.log N)^(1/4 : ℝ)≤Real.log N ∧
      (enhancedCurrentScale N)^2=Real.log N*Real.log (Real.log N) := by
  have hL : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ)<1/4)).comp hL
  have hsmall := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ)<1/2)).tendsto_div_nhds_zero.comp hL
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    enhancedCurrentScale_tendsto.eventually_ge_atTop 1,
    enhancedCurrentScale_tendsto.eventually_ge_atTop (Real.log 3),
    hL.eventually_ge_atTop 1,hpow.eventually_ge_atTop 1024,
    hsmall.eventually_le_const (by norm_num : (0 : ℝ)<1/4)] with N hN ht1 ht3 hLN hp hsm
  have hL0 : 0<Real.log N := by linarith
  have hLL0 : 0≤Real.log (Real.log N) := Real.log_nonneg hLN
  have hscale : (enhancedCurrentScale N)^2=Real.log N*Real.log (Real.log N) :=
    Real.sq_sqrt (mul_nonneg hL0.le hLL0)
  have hlogt : Real.log (Real.log N)≤enhancedCurrentScale N := by
    have hh := Real.log_le_sub_one_of_pos hL0
    have hm := mul_le_mul_of_nonneg_right hh hLL0
    nlinarith
  have hb : Real.log (Real.log N)≤Real.sqrt (Real.log N)/4 := by
    have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hL0 (1/2))).mp hsm
    rw [← Real.sqrt_eq_rpow] at hh
    linarith
  exact ⟨hN,ht1,ht3,hLN,hlogt,hp,sqrt_log_scale_size _ hLN hb,hscale⟩

/-- The extra sqrt(log log N) in the exponent comes from the optimizing
Rankin estimate, rather than from a positive-power arithmetic saving. -/
theorem primeCurrentSquaredError_enhanced_bound :
    ∀ᶠ N : ℕ in atTop, primeCurrentSquaredError N≤
      enhancedCurrentRateConstant*Real.exp (-enhancedCurrentScale N/128) := by
  have hp (k : ℕ) : Tendsto (fun N : ℕ => (enhancedCurrentScale N)^k*
      Real.exp (-(1/128 : ℝ)*enhancedCurrentScale N)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast,Function.comp_apply] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) (1/128)
        (by norm_num)).comp enhancedCurrentScale_tendsto
  have hpoly : Tendsto (fun N : ℕ => (1+enhancedCurrentScale N)^2*
      Real.exp (-enhancedCurrentScale N/128)) atTop (𝓝 0) := by
    have hh := ((hp 2).add ((hp 1).const_mul 2)).add (hp 0)
    simp only [add_zero,mul_zero] at hh
    convert hh using 1
    funext N
    rw [show -enhancedCurrentScale N/128 = -(1/128 : ℝ)*enhancedCurrentScale N by ring]
    ring
  filter_upwards [enhancedCurrentScale_data,hpoly.eventually_le_const zero_lt_one] with N hd hsmall
  obtain ⟨hN,ht1,ht3,hL,hlogL,hpow,hsize,hscale⟩ := hd
  have hb := primeCurrentSquaredError_large_u_scale N hN (enhancedCurrentScale N)
    ht1 ht3 hL hlogL hpow hsize hscale
  have he : Real.exp (-enhancedCurrentScale N/64)=
      Real.exp (-enhancedCurrentScale N/128)*Real.exp (-enhancedCurrentScale N/128) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hb
  have hm := mul_le_mul_of_nonneg_right hsmall
    (show 0≤enhancedCurrentRateConstant*Real.exp (-enhancedCurrentScale N/128) by
      exact mul_nonneg enhancedCurrentRateConstant_pos.le (Real.exp_nonneg _))
  apply hb.trans
  convert hm using 1 <;> ring

lemma enhancedCurrentScale_div_log_tendsto_zero :
    Tendsto (fun N : ℕ => enhancedCurrentScale N/Real.log N) atTop (𝓝 0) := by
  have hL : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ)<1)).tendsto_div_nhds_zero.comp hL
  simp only [Real.rpow_one] at hsmall
  have hs := hsmall.sqrt
  simp only [Real.sqrt_zero] at hs
  apply hs.congr'
  filter_upwards [hL.eventually_ge_atTop 1] with N hLN
  have hL0 : 0<Real.log N := by linarith
  have hLL0 : 0≤Real.log (Real.log N) := Real.log_nonneg hLN
  have ht : 0≤enhancedCurrentScale N := Real.sqrt_nonneg _
  apply (Real.sqrt_eq_iff_eq_sq (div_nonneg hLL0 hL0.le) (div_nonneg ht hL0.le)).mpr
  rw [div_pow,show (enhancedCurrentScale N)^2=Real.log N*Real.log (Real.log N) from
    Real.sq_sqrt (mul_nonneg hL0.le hLL0)]
  field_simp

/-- Limitation of this majorant, not a lower bound on the actual error:
even the enhanced stretched exponential does not beat N to a positive power. -/
theorem enhancedCurrentScale_still_subpower (c δ : ℝ) (hδ : 0<δ) :
    Tendsto (fun N : ℕ => (N : ℝ)^δ*Real.exp (-c*enhancedCurrentScale N))
      atTop atTop := by
  have hsmall := enhancedCurrentScale_div_log_tendsto_zero.const_mul c
  simp only [mul_zero] at hsmall
  have hp : Tendsto (fun N : ℕ => (N : ℝ)^(δ/2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hδ)).comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop_mono' atTop _ hp
  filter_upwards [eventually_gt_atTop (1 : ℕ),
    hsmall.eventually_le_const (half_pos hδ)] with N hN hsm
  have hNr : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hlog : 0<Real.log N := Real.log_pos (by exact_mod_cast hN)
  rw [← mul_div_assoc] at hsm
  have hh := (div_le_iff₀ hlog).mp hsm
  rw [Real.rpow_def_of_pos hNr,Real.rpow_def_of_pos hNr,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

#print axioms primeCurrentSquaredError_large_u_scale
#print axioms primeCurrentSquaredError_enhanced_bound
#print axioms enhancedCurrentScale_still_subpower

end Erdos371
