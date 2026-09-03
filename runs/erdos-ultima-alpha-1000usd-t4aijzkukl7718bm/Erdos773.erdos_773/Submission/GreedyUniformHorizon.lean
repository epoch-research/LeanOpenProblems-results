import Submission.GreedyPhysicalStep

/-!
Uniform scalar hypotheses on a finite horizon imply every one-step
trajectory condition. The exponential growth and decay are evaluated only
at the horizon; no uniform-in-time calculus obligation is left implicit.
-/
namespace Erdos773.GreedyUniformHorizon
open GreedyTrajectoryCalculus GreedyScaledTrajectory GreedyEnvelopeCalculus GreedyPhysicalStep
set_option maxHeartbeats 2500000
noncomputable section

structure Bounds (V d ρ K τ : ℝ) (C : ℕ) : Prop where
  V_pos : 0 < V
  d_one_le : 1 ≤ d
  rho_nonneg : 0 ≤ ρ
  K_large : 4000 ≤ K
  horizon_nonneg : 0 ≤ τ
  step_bound : d ≤ V
  relative_error : ρ*growth K 0 τ ≤ q τ/4
  common_bound : (C:ℝ)+1 ≤ d*ρ
  availability : 5*d*(1+τ)^4 ≤ V*ρ
  curvature : 200*(2+τ)^6*d ≤ V*ρ*(q τ)^2

/-- The small list of horizon bounds is sufficient at every intermediate
    nonnegative real time, hence at every discrete time below the horizon. -/
theorem conditions {V d ρ K τ : ℝ} {C : ℕ} (hb : Bounds V d ρ K τ C)
    {t : ℝ} (ht : 0 ≤ t) (htτ : t ≤ τ) : Conditions V d ρ K t C := by
  have hV := hb.V_pos
  have hd : 0 < d := by linarith only [hb.d_one_le]
  have hρ := hb.rho_nonneg
  have hK : 0 ≤ K := by linarith only [hb.K_large]
  have hτ := hb.horizon_nonneg
  have hqt := q_pos t
  have hqτ := q_pos τ
  have hqmono := q_antitone ht htτ
  have hqτ1 := q_le_one hτ
  have hqt1 := q_le_one ht
  have hw := growth_pos K 0 t
  have hwmono := growth_monotone hK hK ht htτ
  have hw1 : 1 ≤ growth K 0 t := by simpa only [growth_zero] using growth_monotone hK hK (by norm_num : (0:ℝ) ≤ 0) ht
  have hsmall : ρ*growth K 0 t ≤ q t/4 := by
    have hh := (mul_le_mul_of_nonneg_left hwmono hρ).trans hb.relative_error
    linarith only [hh,hqmono]
  have hsmall1 : ρ*growth K 0 t ≤ 1 := by linarith only [hsmall,hqt1]
  have he : E2 d ρ K t ≤ d*q t := by
    dsimp [E2]
    have hh := mul_le_mul_of_nonneg_left hsmall hd.le
    have hhq := mul_nonneg hd.le hqt.le
    nlinarith only [hh,hhq]
  have hcommon : (C:ℝ)+1 ≤ E2 d ρ K t := by
    apply hb.common_bound.trans
    dsimp [E2]
    nlinarith only [mul_le_mul_of_nonneg_left hw1 (mul_nonneg hd.le hρ)]
  have hEQsmall : EQ V ρ K t ≤ Q V t/4 := by
    dsimp [EQ,budgetWeight,Q]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 1+t^2)).mpr
    have hh := mul_le_mul_of_nonneg_left hsmall hV.le
    have hn := mul_nonneg (mul_nonneg hV.le hqt.le) (sq_nonneg t)
    nlinarith only [hh,hn]
  have hpow2 : 1+t^2 ≤ (1+τ)^2 := by
    have hh := pow_le_pow_left₀ ht htτ 2
    nlinarith only [hh,hτ]
  have hupper : 1+F2 d t+E2 d ρ K t ≤ 5*d*(1+τ)^2 := by
    have hF : F2 d t ≤ 3*d*τ^2 := by
      dsimp [F2,a2]
      have hh1 := mul_le_mul_of_nonneg_left hqt1 (show 0 ≤ d*(3*t^2) by positivity)
      have hh2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht htτ 2) (show 0 ≤ 3*d by positivity)
      nlinarith only [hh1,hh2]
    have hE : E2 d ρ K t ≤ d := by
      dsimp [E2]
      nlinarith only [mul_le_mul_of_nonneg_left hsmall1 hd.le]
    have hpoly : 1+3*d*τ^2+d ≤ 5*d*(1+τ)^2 := by
      have hn : 0 ≤ d*τ := mul_nonneg hd.le hτ
      have hn2 : 0 ≤ d*τ^2 := by positivity
      nlinarith only [hb.d_one_le,hn,hn2]
    linarith only [hF,hE,hpoly]
  have hEQlarge : 5*d*(1+τ)^2 ≤ EQ V ρ K t := by
    dsimp [EQ,budgetWeight]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : (0:ℝ) < 1+t^2)).mpr
    have hh := mul_le_mul_of_nonneg_left hpow2 (show 0 ≤ 5*d*(1+τ)^2 by positivity)
    have hg := mul_le_mul_of_nonneg_left hw1 (mul_nonneg hV.le hρ)
    nlinarith only [hh,hg,hb.availability]
  have hcurve : 200*(1+(t+1))^6*d/V ≤ ρ*(q τ)^2 := by
    apply (div_le_iff₀ hV).mpr
    have hp := pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ 1+(t+1))
      (by linarith only [htτ] : 1+(t+1) ≤ 2+τ) 6
    have hh := mul_le_mul_of_nonneg_right hp (show (0:ℝ) ≤ 200*d by positivity)
    nlinarith only [hh,hb.curvature]
  have hq0 : (q τ)^2 ≤ 1 := pow_le_one₀ hqτ.le hqτ1
  have hq1 : (q τ)^2 ≤ q t := by
    have hh := mul_le_mul_of_nonneg_left hqτ1 hqτ.le
    nlinarith only [hh,hqmono]
  have hq2 : (q τ)^2 ≤ (q t)^2 := pow_le_pow_left₀ hqτ.le hqmono 2
  have hc0 : 200*(1+(t+1))^6*d/V ≤ ρ*growth K 0 t := by
    exact hcurve.trans (mul_le_mul_of_nonneg_left (hq0.trans hw1) hρ)
  have hc1 : 200*(1+(t+1))^6*d/V ≤ ρ*growth K 0 t*q t := by
    have hh := mul_le_mul_of_nonneg_right hw1 hqt.le
    have hle : (q τ)^2 ≤ growth K 0 t*q t := hq1.trans (by simpa only [one_mul] using hh)
    nlinarith only [hcurve,mul_le_mul_of_nonneg_left hle hρ]
  have hc2 : 200*(1+(t+1))^6*d/V ≤ ρ*growth K 0 t*(q t)^2 := by
    have hh := mul_le_mul_of_nonneg_right hw1 (sq_nonneg (q t))
    have hle : (q τ)^2 ≤ growth K 0 t*(q t)^2 := hq2.trans (by simpa only [one_mul] using hh)
    nlinarith only [hcurve,mul_le_mul_of_nonneg_left hle hρ]
  refine ⟨hV,hd,hρ,hb.K_large,ht,(div_le_one hV).mpr hb.step_bound,he,hcommon,
    hEQsmall,hupper.trans hEQlarge,?_,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hc0 (show 0 ≤ d^2*q t by positivity)
    dsimp [E2]
    convert hh using 1 <;> ring
  · have hh := mul_le_mul_of_nonneg_left hc1 (show 0 ≤ d^3*q t by positivity)
    dsimp [E2]
    convert hh using 1 <;> ring
  · have hh := mul_le_mul_of_nonneg_left hc2 (show 0 ≤ d^4*q t by positivity)
    dsimp [E2]
    convert hh using 1 <;> ring

/-- A concrete polynomial scale validates the uniform conditions. Here
    d=m^4, the original degree is m^12, and rho=1/m. The lower bound on V
    is compatible with a linear hypergraph of that degree. -/
theorem polynomial_parameters (m V K τ : ℝ) (C : ℕ)
    (hm : 17 ≤ m) (hV : m^12 ≤ V) (hK : 4000 ≤ K) (hτ : 0 ≤ τ)
    (hrelative : 4*growth K 0 τ ≤ m*q τ)
    (havail : 5*(1+τ)^4 ≤ m)
    (hcurve : 200*(2+τ)^6 ≤ m*(q τ)^2)
    (hC : (C:ℝ) ≤ 16*m) : Bounds V (m^4) (1/m) K τ C := by
  have hmpos : 0 < m := by linarith
  have hm1 : 1 ≤ m := by linarith
  have hVp : 0 < V := (pow_pos hmpos 12).trans_le hV
  have hm4 : (1:ℝ) ≤ m^4 := one_le_pow₀ hm1
  have hVρ : m^11 ≤ V*(1/m) := by
    have hh := mul_le_mul_of_nonneg_right hV (by positivity : (0:ℝ) ≤ 1/m)
    convert hh using 1
    field_simp
  have hcommon : (C:ℝ)+1 ≤ m^3 := by
    have hsq := mul_le_mul_of_nonneg_left hm hmpos.le
    have hp := pow_le_pow_right₀ hm1 (show 2 ≤ 3 by omega)
    nlinarith only [hC,hsq,hp,hm1]
  refine ⟨hVp,hm4,by positivity,hK,hτ,?_,?_,?_,?_,?_⟩
  · exact (pow_le_pow_right₀ hm1 (show 4 ≤ 12 by omega)).trans hV
  · have hh : growth K 0 τ/m ≤ q τ/4 := (div_le_iff₀ hmpos).mpr (by linarith only [hrelative])
    convert hh using 1
    ring
  · have he : m^4*(1/m) = m^3 := by field_simp
    rw [he]
    exact hcommon
  · have hh := mul_le_mul_of_nonneg_left havail (pow_nonneg hmpos.le 4)
    have hp := pow_le_pow_right₀ hm1 (show 5 ≤ 11 by omega)
    nlinarith only [hh,hp,hVρ]
  · have hh := mul_le_mul_of_nonneg_left hcurve (pow_nonneg hmpos.le 4)
    have hp := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hm1 (show 5 ≤ 11 by omega)) (sq_nonneg (q τ))
    have hq := mul_le_mul_of_nonneg_right hVρ (sq_nonneg (q τ))
    nlinarith only [hh,hp,hq]

lemma polynomial_le_exp (c x : ℝ) (n : ℕ) (hx : 0 ≤ x) :
    c*x^n ≤ Real.exp (c+(n:ℝ)*x) := by
  have hc : c ≤ Real.exp c := by linarith only [Real.add_one_le_exp c]
  have hx' : x ≤ Real.exp x := by linarith only [Real.add_one_le_exp x]
  have hh := mul_le_mul hc (pow_le_pow_left₀ hx hx' n) (pow_nonneg hx n) (Real.exp_pos c).le
  simpa only [Real.exp_add,Real.exp_nat_mul] using hh

/-- An explicit threshold permits logarithmically growing horizons, rather
    than only one fixed horizon. It is deliberately numerically generous:
    m >= exp(10000*(1+tau)^3) suffices for every scalar profile condition. -/
theorem exponential_threshold (m V τ : ℝ) (C : ℕ) (hτ : 0 ≤ τ)
    (hm : Real.exp (10000*(1+τ)^3) ≤ m) (hV : m^12 ≤ V) (hC : (C:ℝ) ≤ 16*m) :
    Bounds V (m^4) (1/m) 4000 τ C := by
  have hp : (1:ℝ) ≤ (1+τ)^3 := one_le_pow₀ (by linarith : (1:ℝ) ≤ 1+τ)
  have h17 : 17 ≤ m := by
    have hh := Real.add_one_le_exp (10000*(1+τ)^3)
    linarith only [hp,hh,hm]
  have hrel : 4*growth 4000 0 τ ≤ m*q τ := by
    have h4 : (4:ℝ) ≤ Real.exp 4 := by linarith only [Real.add_one_le_exp 4]
    calc
      _ ≤ Real.exp 4*growth 4000 0 τ := mul_le_mul_of_nonneg_right h4 (growth_pos _ _ _).le
      _ ≤ Real.exp (10000*(1+τ)^3)*q τ := by
        rw [growth,q,← Real.exp_add,← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith only [hτ,sq_nonneg τ,pow_nonneg hτ 3]
      _ ≤ _ := mul_le_mul_of_nonneg_right hm (q_pos τ).le
  have hav : 5*(1+τ)^4 ≤ m := by
    apply (polynomial_le_exp 5 (1+τ) 4 (by positivity)).trans
    apply le_trans _ hm
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hτ,sq_nonneg τ,pow_nonneg hτ 3]
  have hcurve : 200*(2+τ)^6 ≤ m*(q τ)^2 := by
    calc
      _ ≤ Real.exp (200+(6:ℝ)*(2+τ)) := polynomial_le_exp 200 (2+τ) 6 (by positivity)
      _ ≤ Real.exp (10000*(1+τ)^3)*(q τ)^2 := by
        rw [q,← Real.exp_nat_mul,← Real.exp_add]
        apply Real.exp_le_exp.mpr
        norm_num only [Nat.cast_ofNat]
        nlinarith only [hτ,sq_nonneg τ,pow_nonneg hτ 3]
      _ ≤ _ := mul_le_mul_of_nonneg_right hm (sq_nonneg (q τ))
  exact polynomial_parameters m V 4000 τ C h17 hV (by norm_num) hτ hrel hav hcurve hC

/-- For each fixed finite normalized horizon, all the scalar conditions
    hold eventually on a concrete polynomial parameter family. This is
    not yet a simultaneous concentration or independent-set theorem. -/
theorem eventually_bounds (K τ : ℝ) (hK : 4000 ≤ K) (hτ : 0 ≤ τ) :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ V : ℝ, (m:ℝ)^12 ≤ V → ∀ C : ℕ, (C:ℝ) ≤ 16*m →
      Bounds V ((m:ℝ)^4) (1/(m:ℝ)) K τ C := by
  let B : ℝ := max 17 (max (4*growth K 0 τ/q τ)
    (max (5*(1+τ)^4) (200*(2+τ)^6/(q τ)^2)))
  obtain ⟨N,hN⟩ := exists_nat_ge B
  apply Filter.eventually_atTop.mpr
  refine ⟨N,?_⟩
  intro m hm V hV C hC
  have hNm : (N:ℝ) ≤ m := by exact_mod_cast hm
  have hBm : B ≤ m := hN.trans hNm
  have h17 : (17:ℝ) ≤ m := (le_max_left _ _).trans hBm
  have hrest : max (4*growth K 0 τ/q τ)
      (max (5*(1+τ)^4) (200*(2+τ)^6/(q τ)^2)) ≤ (m:ℝ) := (le_max_right _ _).trans hBm
  have hrel : 4*growth K 0 τ/q τ ≤ (m:ℝ) := (le_max_left _ _).trans hrest
  have htail : max (5*(1+τ)^4) (200*(2+τ)^6/(q τ)^2) ≤ (m:ℝ) := (le_max_right _ _).trans hrest
  have hav : 5*(1+τ)^4 ≤ (m:ℝ) := (le_max_left _ _).trans htail
  have hcurv : 200*(2+τ)^6/(q τ)^2 ≤ (m:ℝ) := (le_max_right _ _).trans htail
  exact polynomial_parameters m V K τ C h17 hV hK hτ
    ((div_le_iff₀ (q_pos τ)).mp hrel) hav
    ((div_le_iff₀ (sq_pos_of_pos (q_pos τ))).mp hcurv) hC

#print axioms exponential_threshold
#print axioms polynomial_parameters
#print axioms eventually_bounds
#print axioms conditions
end
end Erdos773.GreedyUniformHorizon
