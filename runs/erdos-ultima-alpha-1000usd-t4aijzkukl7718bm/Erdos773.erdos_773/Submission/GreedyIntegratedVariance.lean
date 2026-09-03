import Submission.GreedyUniformMoments

/-!
Uniform total increment caps and integrated conditional variance budgets.
The bound V>=d^3 makes squared profile slopes negligible at every degree.
-/
namespace Erdos773.GreedyIntegratedVariance
open Finset GreedyProfileRecords GreedyProfileGuard GreedyGuardControls GreedyUniformMoments
open GreedyTrajectoryCalculus GreedyScaledTrajectory GreedyEnvelopeCalculus
set_option maxHeartbeats 2500000
noncomputable section

def varianceScale (p : Parameters) (C : ℕ) (j : Fin 3) : ℝ :=
  ![((C:ℝ)+1)*p.d^2,p.d^4,p.d^5] j

def integratedScale (p : Parameters) (C : ℕ) (j : Fin 3) : ℝ :=
  ![((C:ℝ)+1)*p.d,p.d^3,p.d^4] j

def varianceFactor (p : Parameters) (τ : ℝ) : ℝ :=
  (1200*(1+τ)^6+2*(speed p τ)^2)/q τ

def integratedFactor (p : Parameters) (τ : ℝ) : ℝ := varianceFactor p τ*(1+τ)

def incrementCap (p : Parameters) (C : ℕ) (τ : ℝ) (j : Fin 3) : ℝ :=
  ![(C:ℝ)+1+speed p τ/p.d,
    (5*(1+τ)^2+speed p τ)*p.d,(5*(1+τ)^2+speed p τ)*p.d] j

lemma scale_nonneg {p : Parameters} (hd : 0 ≤ p.d) (C : ℕ) (j : Fin 3) :
    0 ≤ varianceScale p C j ∧ 0 ≤ integratedScale p C j := by
  fin_cases j <;> dsimp [varianceScale,integratedScale] <;> constructor <;> positivity

lemma scale_identity (p : Parameters) (C : ℕ) (j : Fin 3) :
    varianceScale p C j = p.d*integratedScale p C j := by
  fin_cases j <;> dsimp [varianceScale,integratedScale] <;> ring

lemma speed_pos {p : Parameters} {L T C : ℕ} {τ : ℝ} (hh : Horizon p L T C τ) : 0 < speed p τ := by
  have hK : 0 < p.K := by linarith only [hh.bounds.K_large]
  have hτ : 0 < 1+τ := by linarith only [hh.bounds.horizon_nonneg]
  dsimp [speed]
  positivity

lemma factor_pos {p : Parameters} {τ : ℝ} (hτ : 0 ≤ τ) :
    0 < varianceFactor p τ ∧ 0 < integratedFactor p τ := by
  have hq := q_pos τ
  have ht : 0 < 1+τ := by linarith
  dsimp [varianceFactor,integratedFactor]
  constructor <;> positivity

lemma qmin_lower {p : Parameters} {L T C n : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (hn : n ≤ T) : p.V*q τ/2 ≤ qmin p n := by
  have hc := hh.conditions hn
  have htτ := (time_mono hc.d_pos.le hc.V_pos.le hn).trans hh.time_bound
  have hq := mul_le_mul_of_nonneg_left (q_antitone hc.time_nonneg htτ) hc.V_pos.le
  have hsmall := hc.Q_small
  have hnon := mul_nonneg hc.V_pos.le (q_pos (time p n)).le
  dsimp [Q] at hsmall
  dsimp [qmin,Q]
  linarith only [hq,hsmall,hnon]

lemma raw_variance_bound {p : Parameters} {L T C n : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (hn : n ≤ T) (j : Fin 3) :
    rawVariance p C j n ≤ 300*(1+τ)^6*varianceScale p C j := by
  have hd : 0 ≤ p.d := by linarith only [hh.bounds.d_one_le]
  have hτ := hh.bounds.horizon_nonneg
  have hB : (1:ℝ) ≤ 1+τ := by linarith
  have h2 := uniform_upper_bound hh hn 0
  have h3 := uniform_upper_bound hh hn 1
  have h4 := uniform_upper_bound hh hn 2
  norm_num only [Fin.val_zero,Fin.val_one,Fin.val_two,Nat.reduceAdd,pow_one] at h2 h3 h4
  have h2n := upper_nonneg hh hn 0
  have h3n := upper_nonneg hh hn 1
  have h4n := upper_nonneg hh hn 2
  have hB2 : (1:ℝ) ≤ (1+τ)^2 := one_le_pow₀ hB
  have hdB : (1:ℝ) ≤ p.d*(1+τ)^2 := by nlinarith only [hh.bounds.d_one_le,hB2,mul_nonneg (sub_nonneg.mpr hh.bounds.d_one_le) (sub_nonneg.mpr hB2)]
  have hplus : upper p 0 n+1 ≤ 5*p.d*(1+τ)^2 := by linarith only [h2,hdB]
  have hp24 := pow_le_pow_right₀ hB (show 2 ≤ 4 by omega)
  have hp46 := pow_le_pow_right₀ hB (show 4 ≤ 6 by omega)
  have hC : (0:ℝ) ≤ (C:ℝ)+1 := by positivity
  fin_cases j
  · dsimp [rawVariance,varianceScale]
    have hs := pow_le_pow_left₀ h2n h2 2
    have hmid : 2*upper p 1 n+(upper p 0 n)^2 ≤ 24*p.d^2*(1+τ)^4 := by
      have hp := mul_le_mul_of_nonneg_left hp24 (show 0 ≤ 8*p.d^2 by positivity)
      nlinarith only [h3,hs,hp]
    have hm := mul_le_mul_of_nonneg_left hmid hC
    have hp := mul_le_mul_of_nonneg_left hp46 (show 0 ≤ 24*p.d^2*((C:ℝ)+1) by positivity)
    have hz : 0 ≤ ((C:ℝ)+1)*p.d^2*(1+τ)^6 := by positivity
    nlinarith only [hm,hp,hz]
  · dsimp [rawVariance,varianceScale]
    have hterm := mul_le_mul hplus h3 h3n (by positivity : (0:ℝ) ≤ 5*p.d*(1+τ)^2)
    have hinner : 3*upper p 2 n+2*(upper p 0 n+1)*upper p 1 n ≤ 52*p.d^3*(1+τ)^4 := by
      have hp := mul_le_mul_of_nonneg_left hp24 (show 0 ≤ 12*p.d^3 by positivity)
      nlinarith only [h4,hterm,hp]
    have hm := mul_le_mul hplus hinner
      (by positivity : (0:ℝ) ≤ 3*upper p 2 n+2*(upper p 0 n+1)*upper p 1 n)
      (by positivity : (0:ℝ) ≤ 5*p.d*(1+τ)^2)
    have hz : 0 ≤ p.d^4*(1+τ)^6 := by positivity
    nlinarith only [hm,hz]
  · dsimp [rawVariance,varianceScale]
    have hs := pow_le_pow_left₀ (by linarith only [h2n] : 0 ≤ upper p 0 n+1) hplus 2
    have hm := mul_le_mul hs h4 h4n (by positivity : (0:ℝ) ≤ (5*p.d*(1+τ)^2)^2)
    nlinarith only [hm]

lemma scaled_slope_square {p : Parameters} (hd : 1 ≤ p.d) (hV : p.d^3 ≤ p.V)
    (C : ℕ) (j : Fin 3) : (p.d^(j.val+1)*(p.d/p.V))^2 ≤ varianceScale p C j/p.V := by
  have hdp : 0 < p.d := by linarith
  have hVp : 0 < p.V := (pow_pos hdp 3).trans_le hV
  have hd2 : p.d^2 ≤ p.V := (pow_le_pow_right₀ hd (show 2 ≤ 3 by omega)).trans hV
  have hrat2 : p.d^2/p.V ≤ 1 := (div_le_one hVp).mpr hd2
  have hrat3 : p.d^3/p.V ≤ 1 := (div_le_one hVp).mpr hV
  have hs2 : (p.d^2/p.V)^2 ≤ p.d^2/p.V := by
    nlinarith only [mul_nonneg (div_nonneg (sq_nonneg p.d) hVp.le) (sub_nonneg.mpr hrat2)]
  have hs3 : (p.d^3/p.V)^2 ≤ p.d^3/p.V := by
    nlinarith only [mul_nonneg (div_nonneg (pow_nonneg hdp.le 3) hVp.le) (sub_nonneg.mpr hrat3)]
  fin_cases j
  · dsimp [varianceScale]
    have hC : 0 ≤ (C:ℝ)*(p.d^2/p.V) := by positivity
    ring_nf at hs2 hC ⊢
    nlinarith only [hs2,hC]
  · dsimp [varianceScale]
    have hm := mul_le_mul_of_nonneg_left hs2 (sq_nonneg p.d)
    convert hm using 1 <;> ring
  · dsimp [varianceScale]
    have hm := mul_le_mul_of_nonneg_left hs3 (sq_nonneg p.d)
    convert hm using 1 <;> ring

/-- A time-uniform bound on the actual recorded error's conditional variance. -/
theorem variance_bound {p : Parameters} {L T C n : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (hV : p.d^3 ≤ p.V) (hn : n < T) (j : Fin 3) (lower : Bool) :
    variance p C j lower n ≤ varianceFactor p τ*varianceScale p C j/p.V := by
  have hd : 0 < p.d := by linarith only [hh.bounds.d_one_le]
  have hVp := hh.bounds.V_pos
  have hq := q_pos τ
  have hscale := (scale_nonneg hd.le C j).1
  have hraw := raw_variance_bound hh hn.le j
  have hqmin := qmin_lower hh hn.le
  have hslope := signed_slope_bound hh hn j lower
  have hsq : (signedProfile p j lower (n+1)-signedProfile p j lower n)^2 ≤
      (speed p τ)^2*(varianceScale p C j/p.V) := by
    have hh1 := pow_le_pow_left₀ (abs_nonneg _) hslope 2
    rw [sq_abs] at hh1
    have hh2 := mul_le_mul_of_nonneg_left (scaled_slope_square hh.bounds.d_one_le hV C j) (sq_nonneg (speed p τ))
    nlinarith only [hh1,hh2]
  have hrdiv : rawVariance p C j n/qmin p n ≤
      (300*(1+τ)^6*varianceScale p C j)/(p.V*q τ/2) :=
    (div_le_div_of_nonneg_right hraw (qmin_pos hh hn.le).le).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hqmin)
  have hq1 := q_le_one hh.bounds.horizon_nonneg
  have hden : p.V*q τ ≤ p.V := by nlinarith only [mul_le_mul_of_nonneg_left hq1 hVp.le]
  have hdiv : varianceScale p C j/p.V ≤ varianceScale p C j/(p.V*q τ) :=
    div_le_div_of_nonneg_left hscale (mul_pos hVp hq) hden
  have hsq' := hsq.trans (mul_le_mul_of_nonneg_left hdiv (sq_nonneg (speed p τ)))
  unfold variance
  calc
    _ ≤ 2*((300*(1+τ)^6*varianceScale p C j)/(p.V*q τ/2))+
        2*((speed p τ)^2*(varianceScale p C j/(p.V*q τ))) := by linarith only [hrdiv,hsq']
    _ = _ := by dsimp [varianceFactor]; field_simp; ring

/-- Sum of all T conditional second-moment bounds, with V cancelled. -/
theorem integrated_variance {p : Parameters} {L T C : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (hV : p.d^3 ≤ p.V) (j : Fin 3) (lower : Bool) :
    (∑ n ∈ range T, variance p C j lower n) ≤ integratedFactor p τ*integratedScale p C j := by
  have hd : 0 ≤ p.d := by linarith only [hh.bounds.d_one_le]
  have hfactor := (factor_pos (p := p) hh.bounds.horizon_nonneg).1.le
  have hscale := (scale_nonneg hd C j).2
  calc
    _ ≤ ∑ _n ∈ range T, varianceFactor p τ*varianceScale p C j/p.V :=
      sum_le_sum (fun n hn => variance_bound hh hV (mem_range.mp hn) j lower)
    _ = (time p T)*varianceFactor p τ*integratedScale p C j := by
      rw [sum_const,card_range,nsmul_eq_mul,scale_identity]
      dsimp [time]
      ring
    _ ≤ τ*varianceFactor p τ*integratedScale p C j :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh.time_bound hfactor) hscale
    _ ≤ _ := by
      have hn := mul_nonneg hfactor hscale
      dsimp [integratedFactor]
      nlinarith only [hn]

/-- Explicit caps for both signs and every vertex. -/
theorem increment_cap {p : Parameters} {L T C n : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (hV : p.d^3 ≤ p.V) (hn : n < T) (j : Fin 3) (lower : Bool) :
    rawCap p C j n+|signedProfile p j lower (n+1)-signedProfile p j lower n| ≤ incrementCap p C τ j := by
  have hd : 0 < p.d := by linarith only [hh.bounds.d_one_le]
  have hVp := hh.bounds.V_pos
  have hS := (speed_pos hh).le
  have hU := uniform_upper_bound hh hn.le 0
  norm_num only [Fin.val_zero,Nat.reduceAdd,pow_one] at hU
  have hB : (1:ℝ) ≤ (1+τ)^2 := one_le_pow₀ (by linarith only [hh.bounds.horizon_nonneg] : (1:ℝ) ≤ 1+τ)
  have hdB : (1:ℝ) ≤ p.d*(1+τ)^2 := by nlinarith only [hh.bounds.d_one_le,hB,mul_nonneg (sub_nonneg.mpr hh.bounds.d_one_le) (sub_nonneg.mpr hB)]
  have hplus : upper p 0 n+1 ≤ 5*p.d*(1+τ)^2 := by linarith only [hU,hdB]
  have hsl := signed_slope_bound hh hn j lower
  have h2 : p.d^2/p.V ≤ 1/p.d := (div_le_div_iff₀ hVp hd).mpr (by nlinarith only [hV])
  have h3 : p.d^3/p.V ≤ p.d := ((div_le_one hVp).mpr hV).trans hh.bounds.d_one_le
  have h4 : p.d^4/p.V ≤ p.d := (div_le_iff₀ hVp).mpr (by
    have hh' := mul_le_mul_of_nonneg_left hV hd.le
    nlinarith only [hh'])
  fin_cases j <;> dsimp [incrementCap,rawCap] at *
  · have hm := mul_le_mul_of_nonneg_left h2 hS
    have hsl' : |signedProfile p 0 lower (n+1)-signedProfile p 0 lower n| ≤ speed p τ / p.d := by
      calc
        _ ≤ speed p τ * p.d^1 * (p.d/p.V) := hsl
        _ = speed p τ * (p.d^2/p.V) := by ring
        _ ≤ speed p τ * (1/p.d) := hm
        _ = _ := by ring
    linarith only [hsl']
  · have hm := mul_le_mul_of_nonneg_left h3 hS
    have hsl' : |signedProfile p 1 lower (n+1)-signedProfile p 1 lower n| ≤ speed p τ * p.d := by
      calc
        _ ≤ speed p τ * p.d^2 * (p.d/p.V) := hsl
        _ = speed p τ * (p.d^3/p.V) := by ring
        _ ≤ _ := hm
    nlinarith only [hsl',hplus]
  · have hm := mul_le_mul_of_nonneg_left h4 hS
    have hsl' : |signedProfile p 2 lower (n+1)-signedProfile p 2 lower n| ≤ speed p τ * p.d := by
      calc
        _ ≤ speed p τ * p.d^3 * (p.d/p.V) := hsl
        _ = speed p τ * (p.d^4/p.V) := by ring
        _ ≤ _ := hm
    nlinarith only [hsl',hplus]

lemma increment_cap_pos {p : Parameters} {L T C : ℕ} {τ : ℝ}
    (hh : Horizon p L T C τ) (j : Fin 3) : 0 < incrementCap p C τ j := by
  have hd : 0 < p.d := by linarith only [hh.bounds.d_one_le]
  have hS := speed_pos hh
  fin_cases j <;> dsimp [incrementCap] <;> positivity

#print axioms raw_variance_bound
#print axioms variance_bound
#print axioms integrated_variance
#print axioms increment_cap
#print axioms increment_cap_pos
end
end Erdos773.GreedyIntegratedVariance
