import Submission.GreedyGuardControls

/-!
Uniform degree and signed-profile slope bounds on a verified horizon.
These estimates will be summed to bound the actual conditional variances.
-/
namespace Erdos773.GreedyUniformMoments
open GreedyProfileRecords GreedyProfileGuard GreedyGuardControls
open GreedyTrajectoryCalculus GreedyEnvelopeCalculus GreedyScaledTrajectory
set_option maxHeartbeats 2500000
noncomputable section

lemma growth_le_top {K r x τ : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    (hx : 0 ≤ x) (hxτ : x ≤ τ) : growth K r x ≤ growth K 0 τ := by
  apply le_trans _ (growth_monotone hK hK hx hxτ)
  apply Real.exp_le_exp.mpr
  have hh := mul_nonneg hr (pow_nonneg hx 3)
  nlinarith only [hh]

lemma growth_derivative_bound {K r x τ : ℝ} (hK : 3 ≤ K) (hr : 0 ≤ r) (hr2 : r ≤ 2)
    (hx : 0 ≤ x) (hxτ : x ≤ τ) :
    |dgrowth K r x| ≤ 4*K*(1+τ)^2*growth K 0 τ := by
  have hK0 : 0 ≤ K := by linarith
  have hKr : 0 ≤ K-r := by linarith
  have hτ : 0 ≤ τ := hx.trans hxτ
  have hc0 : 0 ≤ 3*(K-r)*x^2+K := by positivity
  have hc : 3*(K-r)*x^2+K ≤ 4*K*(1+τ)^2 := by
    have h1 := mul_le_mul_of_nonneg_right (sub_le_self K hr) (sq_nonneg x)
    have h2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxτ 2) hK0
    have h3 := mul_nonneg hK0 hτ
    have h4 := mul_nonneg hK0 (sq_nonneg τ)
    nlinarith only [h1,h2,h3,h4,hK0]
  rw [dgrowth,abs_of_nonneg (mul_nonneg hc0 (growth_pos _ _ _).le)]
  exact mul_le_mul hc (growth_le_top hK0 hr hx hxτ) (growth_pos _ _ _).le (by positivity)

lemma envelope_formula (p : Parameters) (j : Fin 3) (t : ℝ) :
    envelope p j t = p.d^(j.val+1)*p.rho*growth p.K j.val t := by
  fin_cases j <;> norm_num [envelope,E2,E3,E4]

def speed (p : Parameters) (τ : ℝ) : ℝ := (30+4*p.K)*(1+τ)^4

lemma uniform_width_bound {p : Parameters} {L T C : ℕ} {τ t : ℝ}
    (hh : Horizon p L T C τ) (ht : 0 ≤ t) (htτ : t ≤ τ) (j : Fin 3) :
    envelope p j t ≤ p.d^(j.val+1) := by
  have hd : 0 ≤ p.d := by linarith only [hh.bounds.d_one_le]
  have hK : 0 ≤ p.K := by linarith only [hh.bounds.K_large]
  have hρ := hh.bounds.rho_nonneg
  have hg := growth_le_top hK (by positivity : (0:ℝ) ≤ j.val) ht htτ
  have hr : p.rho*growth p.K j.val t ≤ 1 := by
    have hh' := (mul_le_mul_of_nonneg_left hg hρ).trans hh.bounds.relative_error
    have hq := q_le_one hh.bounds.horizon_nonneg
    linarith only [hh',hq]
  rw [envelope_formula]
  have hh' := mul_le_mul_of_nonneg_left hr (pow_nonneg hd (j.val+1))
  nlinarith only [hh']

lemma uniform_profile_bound {p : Parameters} (hd : 0 ≤ p.d) {τ t : ℝ}
    (ht : 0 ≤ t) (htτ : t ≤ τ) (j : Fin 3) : profile p j t ≤ 3*p.d^(j.val+1)*(1+τ)^2 := by
  have hτ : 0 ≤ τ := ht.trans htτ
  have hq := q_le_one ht
  have hqp := (q_pos t).le
  have hq2 : (q t)^2 ≤ 1 := pow_le_one₀ hqp hq
  have hq3 : (q t)^3 ≤ 1 := pow_le_one₀ hqp hq
  have ht2 : t^2 ≤ (1+τ)^2 := power_envelope ht htτ (by omega : 2 ≤ 2)
  have ht1 : t ≤ (1+τ)^2 := by simpa using power_envelope ht htτ (by omega : 1 ≤ 2)
  have hone : (1:ℝ) ≤ (1+τ)^2 := one_le_pow₀ (by linarith : (1:ℝ) ≤ 1+τ)
  fin_cases j
  · change p.d*(3*t^2*q t) ≤ 3*p.d^1*(1+τ)^2
    have hmul := mul_le_mul ht2 hq hqp (by positivity : (0:ℝ) ≤ (1+τ)^2)
    have hh := mul_le_mul_of_nonneg_left hmul (show 0 ≤ 3*p.d by positivity)
    nlinarith only [hh]
  · change p.d^2*(3*t*(q t)^2) ≤ 3*p.d^2*(1+τ)^2
    have hmul := mul_le_mul ht1 hq2 (sq_nonneg (q t)) (by positivity : (0:ℝ) ≤ (1+τ)^2)
    have hh := mul_le_mul_of_nonneg_left hmul (show 0 ≤ 3*p.d^2 by positivity)
    nlinarith only [hh]
  · change p.d^3*(q t)^3 ≤ 3*p.d^3*(1+τ)^2
    have hmul := mul_le_mul_of_nonneg_left (hq3.trans hone) (pow_nonneg hd 3)
    have hn : 0 ≤ p.d^3*(1+τ)^2 := by positivity
    nlinarith only [hmul,hn]

lemma uniform_upper_bound {p : Parameters} {L T C n : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (hn : n ≤ T) (j : Fin 3) :
    upper p j n ≤ 4*p.d^(j.val+1)*(1+τ)^2 := by
  have hc := hh.conditions hn
  have htτ := (time_mono hc.d_pos.le hc.V_pos.le hn).trans hh.time_bound
  have hF := uniform_profile_bound hc.d_pos.le hc.time_nonneg htτ j
  have hE := uniform_width_bound hh hc.time_nonneg htτ j
  have hone : (1:ℝ) ≤ (1+τ)^2 := one_le_pow₀ (by linarith only [hh.bounds.horizon_nonneg] : (1:ℝ) ≤ 1+τ)
  have hm := mul_le_mul_of_nonneg_left hone (pow_nonneg hc.d_pos.le (j.val+1))
  dsimp [upper,center,width]
  nlinarith only [hF,hE,hm]

lemma profile_increment_uniform {p : Parameters} (hd : 0 ≤ p.d) {x y τ : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hyτ : y ≤ τ) (j : Fin 3) :
    |profile p j y-profile p j x| ≤ 30*(1+τ)^4*p.d^(j.val+1)*(y-x) := by
  have hb (z : ℝ) (hz : z ∈ Set.Icc x y) := first_derivative_bounds (hx.trans hz.1) (hz.2.trans hyτ)
  have h2 := increment_abs a2 da2 x y (30*(1+τ)^4) hxy
    (fun z _ => hasDerivAt_a2 z) (fun z hz => (hb z hz).1)
  have h3 := increment_abs a3 da3 x y (30*(1+τ)^4) hxy
    (fun z _ => hasDerivAt_a3 z) (fun z hz => (hb z hz).2.1)
  have h4 := increment_abs a4 da4 x y (30*(1+τ)^4) hxy
    (fun z _ => hasDerivAt_a4 z) (fun z hz => (hb z hz).2.2)
  fin_cases j <;> dsimp [profile,F2,F3,F4]
  · rw [← mul_sub,abs_mul,abs_of_nonneg hd]
    nlinarith only [mul_le_mul_of_nonneg_left h2 hd]
  · rw [← mul_sub,abs_mul,abs_of_nonneg (sq_nonneg p.d)]
    nlinarith only [mul_le_mul_of_nonneg_left h3 (sq_nonneg p.d)]
  · rw [← mul_sub,abs_mul,abs_of_nonneg (pow_nonneg hd 3)]
    nlinarith only [mul_le_mul_of_nonneg_left h4 (pow_nonneg hd 3)]

lemma envelope_increment_uniform {p : Parameters} {L T C : ℕ} {τ x y : ℝ}
    (hh : Horizon p L T C τ) (hx : 0 ≤ x) (hxy : x ≤ y) (hyτ : y ≤ τ) (j : Fin 3) :
    |envelope p j y-envelope p j x| ≤ 4*p.K*(1+τ)^2*p.d^(j.val+1)*(y-x) := by
  have hd : 0 ≤ p.d := by linarith only [hh.bounds.d_one_le]
  have hK : 3 ≤ p.K := by linarith only [hh.bounds.K_large]
  have hK0 : 0 ≤ p.K := by linarith
  have hρ := hh.bounds.rho_nonneg
  have hr : (j.val:ℝ) ≤ 2 := by exact_mod_cast (show j.val ≤ 2 by omega)
  have hi := increment_abs (growth p.K j.val) (dgrowth p.K j.val) x y
    (4*p.K*(1+τ)^2*growth p.K 0 τ) hxy
    (fun z _ => hasDerivAt_growth p.K j.val z)
    (fun z hz => growth_derivative_bound hK (by positivity) hr (hx.trans hz.1) (hz.2.trans hyτ))
  rw [envelope_formula,envelope_formula,← mul_sub,abs_mul,
    abs_of_nonneg (mul_nonneg (pow_nonneg hd _) hρ)]
  have hscaled := mul_le_mul_of_nonneg_left hi (mul_nonneg (pow_nonneg hd (j.val+1)) hρ)
  have hρW : p.rho*growth p.K 0 τ ≤ 1 := by
    have hq := q_le_one hh.bounds.horizon_nonneg
    linarith only [hh.bounds.relative_error,hq]
  have hdiff : 0 ≤ y-x := sub_nonneg.mpr hxy
  have hscaled2 := mul_le_mul_of_nonneg_left hρW
    (show 0 ≤ 4*p.K*(1+τ)^2*p.d^(j.val+1)*(y-x) by positivity)
  nlinarith only [hscaled,hscaled2]

/-- One cap for both signed profile slopes, uniform over all T steps. -/
theorem signed_slope_bound {p : Parameters} {L T C n : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (hn : n < T) (j : Fin 3) (lower : Bool) :
    |signedProfile p j lower (n+1)-signedProfile p j lower n| ≤
      speed p τ*p.d^(j.val+1)*(p.d/p.V) := by
  have hc := hh.conditions hn.le
  have hd := hc.d_pos
  have hV := hc.V_pos
  have htime : time p n ≤ time p (n+1) := time_mono hc.d_pos.le hc.V_pos.le (by omega)
  have htop := (time_mono hc.d_pos.le hc.V_pos.le (show n+1 ≤ T by omega)).trans hh.time_bound
  have hf := profile_increment_uniform hc.d_pos.le hc.time_nonneg htime htop j
  have he := envelope_increment_uniform hh hc.time_nonneg htime htop j
  have hdiff : time p (n+1)-time p n = p.d/p.V := by rw [time_step]; ring
  rw [hdiff] at hf he
  have hid : signedProfile p j lower (n+1)-signedProfile p j lower n =
      (center p j (n+1)-center p j n)+sign lower*(width p j (n+1)-width p j n) := by
    dsimp [signedProfile]
    ring
  rw [hid]
  have ha := abs_add_le (center p j (n+1)-center p j n) (sign lower*(width p j (n+1)-width p j n))
  rw [abs_mul,sign_abs,one_mul] at ha
  have hp := pow_le_pow_right₀ (by linarith only [hh.bounds.horizon_nonneg] : (1:ℝ) ≤ 1+τ) (show 2 ≤ 4 by omega)
  have hm := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 4*p.K*p.d^(j.val+1)*(p.d/p.V) by
      have hK : 0 ≤ p.K := by linarith only [hh.bounds.K_large]
      positivity)
  dsimp [center,width] at ha
  dsimp [speed,center,width]
  nlinarith only [ha,hf,he,hm]

#print axioms uniform_upper_bound
#print axioms profile_increment_uniform
#print axioms envelope_increment_uniform
#print axioms signed_slope_bound
end
end Erdos773.GreedyUniformMoments
