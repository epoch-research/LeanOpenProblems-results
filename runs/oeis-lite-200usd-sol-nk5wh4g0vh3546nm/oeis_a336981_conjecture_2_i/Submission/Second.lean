import Submission.Cubic

open Set Filter MeasureTheory
namespace Elliptic
local notation "r3" => Real.sqrt 3
local notation "r5" => Real.sqrt 5
local notation "r15" => Real.sqrt 15

noncomputable def Jfun (m t : ℝ) : ℝ :=
  m*t^2/(1+t^2) * (Real.sqrt ((1+t^2)*(1+(1-m)*t^2)))⁻¹
noncomputable def Ji (m : ℝ) : ℝ := ∫ t in Ioi (0:ℝ), Jfun m t

noncomputable def cubAlpha : ℝ := (r3/6-1/4)*r5+r3/6-1/4
noncomputable def cubBeta : ℝ := (r5+3)/2
noncomputable def cubPole : ℝ := r15/6-r3/12-1/2
noncomputable def cubRC : ℝ := -2*r5/3-2
noncomputable def cubQR (t : ℝ) : ℝ :=
  cubMul/2*cubRC*mm1*t*(1+(1-mm1)*t^2) /
    (cubPole*(1+t^2)+mm1*t^2)
noncomputable def cubQRD (t : ℝ) : ℝ :=
  let L := 1+(1-mm1)*t^2
  let den := cubPole*(1+t^2)+mm1*t^2
  cubMul/2*cubRC*mm1 *
    ((1+3*(1-mm1)*t^2)*den - t*L*(2*(cubPole+mm1)*t)) / den^2
noncomputable def cubExact (t : ℝ) : ℝ :=
  cubQR t * (Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2)))⁻¹

lemma cubPole_pos : 0 < cubPole ∧ 0 < cubPole+mm1 := by
  rcases radical_bounds with ⟨h3l,h3u,h5l,h5u,h15l,h15u⟩
  dsimp [cubPole, mm1]
  constructor <;> linarith

lemma cubQR_den_pos (t : ℝ) : 0 < cubPole*(1+t^2)+mm1*t^2 := by
  have hp := cubPole_pos.1
  have hm := mm_bounds.1
  nlinarith [sq_nonneg t, mul_nonneg hm (sq_nonneg t),
    mul_nonneg hp.le (by positivity : (0:ℝ) ≤ 1+t^2)]

lemma cubQR_deriv (t : ℝ) : HasDerivAt cubQR (cubQRD t) t := by
  let c := cubMul/2*cubRC*mm1
  let L : ℝ → ℝ := fun x => 1+(1-mm1)*x^2
  let d : ℝ → ℝ := fun x => cubPole*(1+x^2)+mm1*x^2
  have hL : HasDerivAt L (2*(1-mm1)*t) t := by
    dsimp [L]
    convert ((hasDerivAt_const t (1-mm1)).mul ((hasDerivAt_id t).pow 2)).const_add 1 using 1 <;>
      simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.pow_apply] <;> ring
  have hd' : HasDerivAt d (2*(cubPole+mm1)*t) t := by
    dsimp [d]
    convert (((hasDerivAt_const t cubPole).mul (((hasDerivAt_id t).pow 2).const_add 1)).add
      ((hasDerivAt_const t mm1).mul ((hasDerivAt_id t).pow 2))) using 1 <;>
      simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.pow_apply] <;> ring
  have hn := ((hasDerivAt_const t c).mul (hasDerivAt_id t) |>.mul hL)
  have hd : d t ≠ 0 := by dsimp [d]; exact (cubQR_den_pos t).ne'
  have hh := hn.div hd' hd
  convert hh using 1 <;>
    simp only [cubQR, cubQRD, c, L, d, id_eq, Pi.mul_apply, Pi.add_apply, Pi.pow_apply] <;>
    field_simp [hd] <;> ring

lemma sourceR_pos (t : ℝ) : 0 < (1+t^2)*(1+(1-mm1)*t^2) := by
  have hm := mm_bounds.2.1
  apply mul_pos <;> nlinarith [sq_nonneg t,
    mul_nonneg (sub_pos.mpr hm).le (sq_nonneg t)]

lemma sourceG_deriv (t : ℝ) : HasDerivAt
    (fun x : ℝ => (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹)
    (-(t*(2-mm1+2*(1-mm1)*t^2) /
      ((1+t^2)*(1+(1-mm1)*t^2))) *
      (Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2)))⁻¹) t := by
  let R : ℝ → ℝ := fun x => (1+x^2)*(1+(1-mm1)*x^2)
  have hR : HasDerivAt R (2*t*(2-mm1+2*(1-mm1)*t^2)) t := by
    dsimp [R]
    convert ((((hasDerivAt_id t).pow 2).const_add 1).mul
      (((hasDerivAt_const t (1-mm1)).mul ((hasDerivAt_id t).pow 2)).const_add 1)) using 1 <;>
      simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.pow_apply] <;> ring
  have hs := (hR.sqrt (sourceR_pos t).ne').inv (Real.sqrt_ne_zero'.2 (sourceR_pos t))
  have heq : -(t*(2-mm1+2*(1-mm1)*t^2) / (R t)) *
      (Real.sqrt (R t))⁻¹ =
      -(2*t*(2-mm1+2*(1-mm1)*t^2) / (2*Real.sqrt (R t))) /
        Real.sqrt (R t)^2 := by
    have hsquare : Real.sqrt (R t)^2 = R t := Real.sq_sqrt (sourceR_pos t).le
    rw [hsquare]
    ring
  convert hs using 1

noncomputable def cubTargetX (t : ℝ) : ℝ := mm2*(cubS t)^2/(1+(cubS t)^2)
noncomputable def cubSourceX (t : ℝ) : ℝ := mm1*t^2/(1+t^2)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma cub_exact_rational_identity (t : ℝ) :
    cubQRD t - cubQR t * (t*(2-mm1+2*(1-mm1)*t^2) /
      ((1+t^2)*(1+(1-mm1)*t^2))) =
    cubMul*(cubTargetX t-cubAlpha-cubBeta*cubSourceX t) := by
  rcases radical_relations with ⟨h3,h5,h15⟩
  have hd1 := (cubQR_den_pos t).ne'
  have hd2 : t^2+cubB ≠ 0 := by
    have hb := cub_constants_pos.2.2.1
    nlinarith [sq_nonneg t]
  have hr := (sourceR_pos t).ne'
  have hone : 1+t^2 ≠ 0 := by positivity
  have hL : 1+(1-mm1)*t^2 ≠ 0 := by
    have hm := mm_bounds.2.1
    nlinarith [sq_nonneg t, mul_nonneg (sub_pos.mpr hm).le (sq_nonneg t)]

  have hs : 1+(cubS t)^2 ≠ 0 := by positivity
  unfold cubQRD cubQR cubTargetX cubSourceX
  dsimp only
  field_simp [hd1, hr, hone, hL, hs]
  unfold cubS
  field_simp [hd2]
  dsimp [cubAlpha, cubBeta, cubPole, cubRC, cubMul, cubC, cubA, cubB,
    mm1, mm2]
  dsimp [cubPole, cubRC, cubMul, cubC, cubA, cubB, mm1, mm2, cubS] at hd1 hd2 hr hs hL
  field_simp [hd1, hd2, hr, hone, hL, hs]

  rw [h15] at *
  ring_nf
  have p33 : r3^3=3*r3 := by
    calc r3^3=r3^2*r3 := by ring
         _=3*r3 := by rw [h3]
  have p34 : r3^4=9 := by
    calc r3^4=(r3^2)^2 := by ring
         _=9 := by rw [h3]; norm_num
  have p35 : r3^5=9*r3 := by
    calc r3^5=r3^4*r3 := by ring
         _=9*r3 := by rw [p34]
  have p36 : r3^6=27 := by
    calc r3^6=(r3^2)^3 := by ring
         _=27 := by rw [h3]; norm_num
  have p53 : r5^3=5*r5 := by
    calc r5^3=r5^2*r5 := by ring
         _=5*r5 := by rw [h5]
  have p54 : r5^4=25 := by
    calc r5^4=(r5^2)^2 := by ring
         _=25 := by rw [h5]; norm_num
  have p55 : r5^5=25*r5 := by
    calc r5^5=r5^4*r5 := by ring
         _=25*r5 := by rw [p54]
  have p56 : r5^6=125 := by
    calc r5^6=(r5^2)^3 := by ring
         _=125 := by rw [h5]; norm_num
  all_goals
    repeat' first | rw [p36] | rw [p35] | rw [p34] | rw [p33] | rw [h3] | rw [p56] | rw [p55] | rw [p54] | rw [p53] | rw [h5]
    ring_nf
    repeat' first | rw [p36] | rw [p35] | rw [p34] | rw [p33] | rw [h3] | rw [p56] | rw [p55] | rw [p54] | rw [p53] | rw [h5]
    ring

lemma cubExact_deriv (t : ℝ) : HasDerivAt cubExact
    (cubMul*(cubTargetX t-cubAlpha-cubBeta*cubSourceX t) *
      (Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2)))⁻¹) t := by
  have hh := (cubQR_deriv t).mul (sourceG_deriv t)
  convert hh using 1
  have hi := cub_exact_rational_identity t
  linear_combination -(Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2)))⁻¹ * hi

lemma Jfun_eq (m t : ℝ) : Jfun m t =
    m*t^2/(1+t^2) * (Real.sqrt ((1+t^2)*(1+(1-m)*t^2)))⁻¹ := rfl

lemma integrableOn_Jfun {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m < 1) :
    IntegrableOn (Jfun m) (Ioi 0) := by
  have hi := integrableOn_Ki hm0 hm1
  apply hi.mono' (by
    unfold Jfun
    fun_prop)
  filter_upwards [] with t
  unfold Jfun
  have hden : 0 < 1+t^2 := by positivity
  have hx0 : 0 ≤ m*t^2/(1+t^2) := div_nonneg (mul_nonneg hm0 (sq_nonneg t)) hden.le
  have hx1 : m*t^2/(1+t^2) ≤ 1 := by
    apply (div_le_one hden).2
    nlinarith [mul_le_mul_of_nonneg_right hm1.le (sq_nonneg t)]
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hx0]
  let z : ℝ := (Real.sqrt ((1+t^2)*(1+(1-m)*t^2)))⁻¹
  calc
    m*t^2/(1+t^2) * ‖z‖ ≤ ‖z‖ := by simpa using mul_le_mul_of_nonneg_right hx1 (norm_nonneg z)
    _ = z := by rw [Real.norm_eq_abs, abs_of_nonneg] <;> positivity

lemma Ki_sub_Ei_eq_Ji {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m < 1) :
    Ki m - Ei m = Ji m := by
  rw [Ki, Ei, Ji, ← MeasureTheory.integral_sub
    (integrableOn_Ki hm0 hm1) (integrableOn_Ei hm0 hm1.le)]
  apply integral_congr_ae
  filter_upwards [] with t
  unfold Jfun
  have hden : 0 < 1+t^2 := by positivity
  have hL : 0 < 1+(1-m)*t^2 := by
    nlinarith [sq_nonneg t, mul_nonneg (sub_pos.mpr hm1).le (sq_nonneg t)]
  have hsden : Real.sqrt (1+t^2) ≠ 0 := (Real.sqrt_pos.2 hden).ne'
  have hsL : Real.sqrt (1+(1-m)*t^2) ≠ 0 := (Real.sqrt_pos.2 hL).ne'
  rw [Real.sqrt_mul hden.le]

  field_simp [hsden, hsL]
  rw [Real.sq_sqrt hden.le]
  have hL' : 0 ≤ 1+t^2*(1-m) := by nlinarith
  rw [Real.sq_sqrt hL']
  field_simp [hsL]
  ring

noncomputable def cubExactNorm (u : ℝ) : ℝ :=
  (cubMul/2*cubRC*mm1) * u * (u^2+(1-mm1)) /
    ((cubPole*(u^2+1)+mm1) *
      Real.sqrt ((u^2+1)*(u^2+(1-mm1))))

lemma cubExact_eq_norm {t : ℝ} (ht : 0 < t) : cubExact t = cubExactNorm t⁻¹ := by
  have ht0 := ht.ne'
  have h1 : 1+t^2 = t^2*((t⁻¹)^2+1) := by field_simp [ht0]
  have hL : 1+(1-mm1)*t^2 = t^2*((t⁻¹)^2+(1-mm1)) := by
    field_simp [ht0]
  have hD : cubPole*(1+t^2)+mm1*t^2 =
      t^2*(cubPole*((t⁻¹)^2+1)+mm1) := by rw [h1]; ring
  have hs : Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2)) =
      t^2 * Real.sqrt (((t⁻¹)^2+1)*((t⁻¹)^2+(1-mm1))) := by
    rw [h1, hL]
    rw [show t^2*(t⁻¹^2+1)*(t^2*(t⁻¹^2+(1-mm1))) =
      t^4*((t⁻¹)^2+1)*((t⁻¹)^2+(1-mm1)) by ring]
    rw [show t^4*((t⁻¹)^2+1)*((t⁻¹)^2+(1-mm1)) =
      t^4*(((t⁻¹)^2+1)*((t⁻¹)^2+(1-mm1))) by ring,
      Real.sqrt_mul (by positivity : (0:ℝ) ≤ t^4)]
    rw [show t^4=(t^2)^2 by ring, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (sq_nonneg t)]
  unfold cubExact cubQR cubExactNorm
  rw [hs, hL, hD]
  have hs0 : Real.sqrt (((t⁻¹)^2+1)*((t⁻¹)^2+(1-mm1))) ≠ 0 := by
    apply (Real.sqrt_pos.2 ?_).ne'
    have hm := mm_bounds.2.1
    apply mul_pos <;> nlinarith [sq_nonneg t⁻¹]
  field_simp [ht0, hs0]

lemma cubExactNorm_continuous : Continuous cubExactNorm := by
  unfold cubExactNorm
  apply Continuous.div₀
  · fun_prop
  · fun_prop
  · intro u
    have hp := cubPole_pos
    have hm := mm_bounds
    have hd : 0 < cubPole*(u^2+1)+mm1 := by
      nlinarith [sq_nonneg u, mul_nonneg hp.1.le (by positivity : (0:ℝ)≤u^2+1)]
    have hr : 0 < (u^2+1)*(u^2+(1-mm1)) := by
      apply mul_pos <;> nlinarith [sq_nonneg u]
    exact (mul_pos hd (Real.sqrt_pos.2 hr)).ne'

lemma cubExact_tendsto_zero : Tendsto cubExact atTop (nhds 0) := by
  have heq : cubExact =ᶠ[atTop] fun t => cubExactNorm t⁻¹ := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    exact cubExact_eq_norm ht
  have hc : Tendsto (fun t : ℝ => cubExactNorm t⁻¹) atTop (nhds (cubExactNorm 0)) :=
    cubExactNorm_continuous.continuousAt.tendsto.comp tendsto_inv_atTop_zero
  have hz : cubExactNorm 0 = 0 := by simp [cubExactNorm]
  rw [hz] at hc
  exact hc.congr' heq.symm

noncomputable def cubDerivFun (t : ℝ) : ℝ :=
  cubMul*(cubTargetX t-cubAlpha-cubBeta*cubSourceX t) *
    (Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2)))⁻¹

lemma cubTargetX_bounds (t : ℝ) : 0 ≤ cubTargetX t ∧ cubTargetX t ≤ 1 := by
  unfold cubTargetX
  have hm0 := mm_bounds.2.2.1
  have hm1 := mm_bounds.2.2.2
  have hd : 0 < 1+(cubS t)^2 := by positivity
  constructor
  · positivity
  apply (div_le_one hd).2
  nlinarith [mul_le_mul_of_nonneg_right hm1.le (sq_nonneg (cubS t))]

lemma Jfun_continuous {m : ℝ} (hm : m < 1) : Continuous (Jfun m) := by
  unfold Jfun
  apply Continuous.mul
  · apply Continuous.div₀
    · exact continuous_const.mul (continuous_id.pow 2)
    · exact continuous_const.add (continuous_id.pow 2)
    · intro t; positivity
  · exact tangent_K_integrand_continuous hm

lemma cubTarget_integrand_continuous : Continuous (fun t => cubTargetX t *
    (Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2)))⁻¹) := by
  apply Continuous.mul
  · unfold cubTargetX
    apply Continuous.div₀
    · exact continuous_const.mul (cubS_continuous.pow 2)
    · exact continuous_const.add (cubS_continuous.pow 2)
    · intro t; positivity
  · exact tangent_K_integrand_continuous mm_bounds.2.1


lemma integrableOn_cubTarget : IntegrableOn (fun t => cubTargetX t *
    (Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2)))⁻¹) (Ioi 0) := by
  apply (integrableOn_Ki mm_bounds.1 mm_bounds.2.1).mono'
    cubTarget_integrand_continuous.aestronglyMeasurable
  filter_upwards [] with t
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (cubTargetX_bounds t).1]
  let z : ℝ := (Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2)))⁻¹
  calc
    cubTargetX t * ‖z‖ ≤ ‖z‖ := by
      simpa using mul_le_mul_of_nonneg_right (cubTargetX_bounds t).2 (norm_nonneg z)
    _ = z := by rw [Real.norm_eq_abs, abs_of_nonneg] <;> positivity

lemma integrableOn_cubDeriv : IntegrableOn cubDerivFun (Ioi 0) := by
  have ht := integrableOn_cubTarget
  have hg := (integrableOn_Ki mm_bounds.1 mm_bounds.2.1).const_mul cubAlpha
  have hj := (integrableOn_Jfun mm_bounds.1 mm_bounds.2.1).const_mul cubBeta
  have hi := (ht.sub hg).sub hj |>.const_mul cubMul
  exact (integrableOn_congr_fun (fun x hx => by
    unfold cubDerivFun cubSourceX Jfun
    simp only [Pi.sub_apply]
    ring) measurableSet_Ioi).2 hi

lemma integral_cubDeriv_zero : ∫ t in Ioi (0:ℝ), cubDerivFun t = 0 := by
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := cubExact) (f' := cubDerivFun) (a := 0) (m := 0)
    (by intro x hx; simpa [cubDerivFun] using cubExact_deriv x)
    integrableOn_cubDeriv cubExact_tendsto_zero
  simpa [cubExact, cubQR] using h

lemma Ji_cubic_isogeny :
    Ji mm2 = cubMul*(cubAlpha*Ki mm1+cubBeta*Ji mm1) := by
  let jt : ℝ → ℝ := Jfun mm2
  have hsub := MeasureTheory.integral_comp_mul_deriv_Ioi
    (f := cubS) (f' := cubD) (g := jt) (a := 0)
    cubS_continuous.continuousOn cubS_tendsto
    (by intro x hx; simpa [cubD] using (cubS_deriv x).hasDerivWithinAt)
    (by exact (Jfun_continuous mm_bounds.2.2.2).continuousOn)
    (by
      have hi : IntegrableOn jt (Ici 0) :=
        (integrableOn_Ici_iff_integrableOn_Ioi).2 (by
          simpa [jt] using integrableOn_Jfun mm_bounds.2.2.1 mm_bounds.2.2.2)
      apply hi.mono_set
      rintro y ⟨x,hx,rfl⟩
      have hs0 : cubS 0 = 0 := by simp [cubS]
      calc 0 = cubS 0 := hs0.symm
           _ ≤ cubS x := cubS_strictMono.monotone hx)
    (by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      have hi := integrableOn_cubTarget.const_mul cubMul
      exact (integrableOn_congr_fun (fun x hx => by
        change jt (cubS x) * cubD x = _
        rw [show jt (cubS x) = cubTargetX x *
          (Real.sqrt ((1+(cubS x)^2)*(1+(1-mm2)*(cubS x)^2)))⁻¹ by
            rfl]
        rw [mul_assoc, cub_pullback]
        ring) measurableSet_Ioi).2 hi)
  have hs0 : cubS 0 = 0 := by simp [cubS]
  rw [hs0] at hsub
  have hpull : (∫ x in Ioi (0:ℝ), (jt ∘ cubS) x * cubD x) =
      cubMul * ∫ x in Ioi (0:ℝ), cubTargetX x *
        (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹ := by
    calc
      _ = ∫ x in Ioi (0:ℝ), cubMul * (cubTargetX x *
          (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹) := by
            apply integral_congr_ae
            filter_upwards [] with x
            change jt (cubS x) * cubD x = _
            rw [show jt (cubS x) = cubTargetX x *
              (Real.sqrt ((1+(cubS x)^2)*(1+(1-mm2)*(cubS x)^2)))⁻¹ by
                rfl]
            rw [mul_assoc, cub_pullback]
            ring
      _ = _ := by rw [MeasureTheory.integral_const_mul]
  rw [hpull] at hsub
  have hzero := integral_cubDeriv_zero
  unfold cubDerivFun at hzero
  rw [show (fun t : ℝ => cubMul *
      (cubTargetX t - cubAlpha - cubBeta * cubSourceX t) *
        (Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2)))⁻¹) =
      (fun t => cubMul * ((cubTargetX t - cubAlpha - cubBeta * cubSourceX t) *
        (Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2)))⁻¹)) by
      funext t; ring] at hzero
  have hint : (∫ x in Ioi (0:ℝ), cubTargetX x *
      (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹) =
      cubAlpha*Ki mm1+cubBeta*Ji mm1 := by
    rw [MeasureTheory.integral_const_mul] at hzero
    have hc := cubMul_pos
    have hinner : ∫ x in Ioi (0:ℝ),
        (cubTargetX x-cubAlpha-cubBeta*cubSourceX x) *
          (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹ = 0 := by
      nlinarith
    have heq : (∫ x in Ioi (0:ℝ),
        (cubTargetX x-cubAlpha-cubBeta*cubSourceX x) *
          (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹) =
        (∫ x in Ioi (0:ℝ), cubTargetX x *
          (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹) -
        (∫ x in Ioi (0:ℝ), cubAlpha *
          (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹) -
        (∫ x in Ioi (0:ℝ), cubBeta * Jfun mm1 x) := by
      calc
        _ = ∫ x in Ioi (0:ℝ),
            (cubTargetX x * (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹ -
              cubAlpha * (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹) -
              cubBeta * Jfun mm1 x := by
                apply integral_congr_ae
                filter_upwards [] with x
                unfold cubSourceX Jfun
                ring
        _ = (∫ x in Ioi (0:ℝ),
              cubTargetX x * (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹ -
              cubAlpha * (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹) -
              (∫ x in Ioi (0:ℝ), cubBeta * Jfun mm1 x) := by
                simpa only [Pi.sub_apply] using
                  (MeasureTheory.integral_sub
                    (integrableOn_cubTarget.sub
                      ((integrableOn_Ki mm_bounds.1 mm_bounds.2.1).const_mul cubAlpha))
                    ((integrableOn_Jfun mm_bounds.1 mm_bounds.2.1).const_mul cubBeta))
        _ = _ := by
          congr 1
          simpa only [Pi.sub_apply] using
            (MeasureTheory.integral_sub integrableOn_cubTarget
              ((integrableOn_Ki mm_bounds.1 mm_bounds.2.1).const_mul cubAlpha))
    rw [heq, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul] at hinner
    simpa [Ki, Ji] using (show
      (∫ x in Ioi (0:ℝ), cubTargetX x *
        (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹) =
        cubAlpha*(∫ x in Ioi (0:ℝ),
          (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹) +
        cubBeta*(∫ x in Ioi (0:ℝ), Jfun mm1 x) by linarith)
  rw [hint] at hsub
  simpa [Ji, jt] using hsub.symm






lemma HE_cubic_isogeny :
    H mm2 - En mm2 = cubMul *
      (cubAlpha * H mm1 + cubBeta * (H mm1 - En mm1)) := by
  unfold H En
  rw [K_eq_Ki mm_bounds.2.2.1 mm_bounds.2.2.2,
    E_eq_Ei mm_bounds.2.2.1 mm_bounds.2.2.2.le,
    K_eq_Ki mm_bounds.1 mm_bounds.2.1,
    E_eq_Ei mm_bounds.1 mm_bounds.2.1.le]
  have h2 := Ki_sub_Ei_eq_Ji mm_bounds.2.2.1 mm_bounds.2.2.2
  have h1 := Ki_sub_Ei_eq_Ji mm_bounds.1 mm_bounds.2.1
  have hj := Ji_cubic_isogeny
  rw [show (2 / Real.pi) * Ki mm2 - (2 / Real.pi) * Ei mm2 =
      (2 / Real.pi) * (Ki mm2 - Ei mm2) by ring,
    h2,
    show (2 / Real.pi) * Ki mm1 - (2 / Real.pi) * Ei mm1 =
      (2 / Real.pi) * (Ki mm1 - Ei mm1) by ring,
    h1, hj]
  ring

