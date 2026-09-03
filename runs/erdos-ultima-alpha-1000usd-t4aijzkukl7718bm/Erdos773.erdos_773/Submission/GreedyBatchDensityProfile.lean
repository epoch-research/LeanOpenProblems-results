import Submission.GreedyBatchRateGeometry

/-! A continuation-density profile with enough slack to pay for all
shrinking-batch discrepancies. The future failure penalty is kept separate. -/
namespace Erdos773.GreedyBatchDensityProfile
open GreedyBatchProfiles GreedyBatchProfileStep GreedyBatchProfileConditions
open GreedyBatchRateGeometry GreedyBatchReward
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section

def efficiency (m : ℕ) : ℝ := 1-1000000/(m:ℝ)
def density (m : ℕ) (S d t : ℝ) : ℝ := efficiency m*(S-t)/d

lemma efficiency_bounds (m : ℕ) (hm : 2000000≤ m) : 1/2≤efficiency m ∧ efficiency m≤1 := by
  have hmR : (2000000:ℝ)≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ)< m := by linarith only [hmR]
  have hh : (1000000:ℝ)/(m:ℝ)≤1/2 := (div_le_iff₀ hm0).mpr (by linarith only [hmR])
  have hz : (0:ℝ)≤1000000/(m:ℝ) := by positivity
  dsimp [efficiency]
  exact ⟨by linarith only [hh],by linarith only [hz]⟩

lemma next_density (m : ℕ) (S d t : ℝ) (hd : d≠0) :
    density m S (nextD m d t) (t+step m t)=
      (efficiency m*(S-(t+step m t))/d)*Real.exp (growth m t) := by
  have he : nextD m d t=d*Real.exp (-growth m t) := by
    dsimp [nextD,growth]
    congr 1
    congr 1
    ring
  unfold density
  rw [he,Real.exp_neg]
  field_simp

lemma future_lower (m : ℕ) (S d t : ℝ) (hm : 2000000≤ m) (hd : 0<d) (hS : t+step m t≤S) :
    (efficiency m*(S-(t+step m t))/d)*(1+growth m t)≤
      density m S (nextD m d t) (t+step m t) := by
  have hell : 0≤efficiency m := le_trans (by norm_num) (efficiency_bounds m hm).1
  have hs : 0≤S-(t+step m t) := sub_nonneg.mpr hS
  rw [next_density m S d t (ne_of_gt hd)]
  have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (growth m t))
    (show 0≤efficiency m*(S-(t+step m t))/d by positivity)
  simpa only [add_comm] using hh

/-- The density profile has a spare p/m per stage, before charging the
explicit union-bound failure penalty. -/
theorem rate_margin (m : ℕ) (S d t : ℝ) (C P : ℕ) (h : Range m d t C P)
    (hmLarge : 2000000≤ m) (hS : t+step m t≤S) (hS3 : S^3≤ m) :
    density m S d t+probability m d t/(m:ℝ)≤
      rate (caps m d t C P) (probability m d t) (density m S (nextD m d t) (t+step m t)) := by
  let ell := efficiency m
  let s := S-(t+step m t)
  let z := load (caps m d t C P) (probability m d t)
  let p := probability m d t
  let u := growth m t
  let hstep := step m t
  have hm := h.m_pos
  have hd := h.d_pos
  have ht : 0≤t := by have := h.t_one; linarith
  have hs : 0≤s := sub_nonneg.mpr hS
  have hs0 : 0≤hstep := (step_pos m t (by have := h.large; omega)).le
  have hell0 : 0≤ell := le_trans (by norm_num) (efficiency_bounds m hmLarge).1
  have hell1 : ell≤1 := (efficiency_bounds m hmLarge).2
  have hcoarse := coarse_load m d t C P h
  have hQ : 0≤1-p-z := by have hh := hcoarse.2.2.2; change p+z≤1 at hh; linarith only [hh]
  have hf := future_lower m S d t hmLarge hd hS
  have hrate : p*(1-z)+(ell*s/d)*(1+u)*(1-p-z)≤
      rate (caps m d t C P) p (density m S (nextD m d t) (t+hstep)) := by
    have hh := mul_le_mul_of_nonneg_right hf hQ
    exact add_le_add le_rfl hh
  have hrateD := mul_le_mul_of_nonneg_right hrate hd.le
  have he : (p*(1-z)+(ell*s/d)*(1+u)*(1-p-z))*d=
      hstep*(1-z)+ell*s*(1+u)*(1-p-z) := by
    dsimp only [p,probability,hstep]
    field_simp
  rw [he] at hrateD
  have htS : t≤S := (le_add_of_nonneg_right hs0).trans hS
  have hS0 : 0≤S := ht.trans htS
  have hsS : s≤S := by dsimp [s]; linarith only [ht,hs0]
  have ht2 : t^2≤S^2 := pow_le_pow_left₀ ht htS 2
  have hsx : s*t^2≤(m:ℝ) := by
    have hh := mul_le_mul hsS ht2 (sq_nonneg t) hS0
    nlinarith only [hh,hS3]
  have hbr := bracket_lower m d t C P h
  change -10000*hstep*t^2/(m:ℝ)^2≤u-(p+z)*(1+u) at hbr
  have hb := mul_le_mul_of_nonneg_left hbr (mul_nonneg hell0 hs)
  have herror : ell*s*(10000*hstep*t^2/(m:ℝ)^2)≤10000*hstep/(m:ℝ) := by
    calc
      _ ≤ s*(10000*hstep*t^2/(m:ℝ)^2) := by
        have hh := mul_le_mul_of_nonneg_right hell1
          (show 0≤s*(10000*hstep*t^2/(m:ℝ)^2) by positivity)
        nlinarith only [hh]
      _ = (10000*hstep/(m:ℝ)^2)*(s*t^2) := by ring
      _ ≤ (10000*hstep/(m:ℝ)^2)*m := mul_le_mul_of_nonneg_left hsx (by positivity)
      _ = _ := by field_simp
  have hbfinal : -10000*hstep/(m:ℝ)≤ell*s*(u-(p+z)*(1+u)) := by
    ring_nf at hb herror ⊢
    nlinarith only [hb,herror]
  have hz : z≤10/(m:ℝ) := by
    have hh : (m:ℝ)≤(m:ℝ)^2 := by have hm1 := h.m_one; nlinarith only [hm1]
    exact hcoarse.2.2.1.trans (div_le_div_of_nonneg_left (by norm_num) hm hh)
  have hzh := mul_le_mul_of_nonneg_left hz hs0
  have hell : hstep*(1-ell)=1000000*hstep/(m:ℝ) := by dsimp [ell,efficiency]; ring
  have hnonneg : 0≤hstep/(m:ℝ) := by positivity
  have henergy : hstep/(m:ℝ)≤hstep*(1-ell)-hstep*z+ell*s*(u-(p+z)*(1+u)) := by
    ring_nf at hzh hell hbfinal hnonneg ⊢
    nlinarith only [hzh,hell,hbfinal,hnonneg]
  have hmain : ell*(s+hstep)+hstep/(m:ℝ)≤
      rate (caps m d t C P) p (density m S (nextD m d t) (t+hstep))*d := by
    nlinarith only [hrateD,henergy]
  apply le_of_mul_le_mul_right ?_ hd
  calc
    (density m S d t+probability m d t/(m:ℝ))*d=ell*(s+hstep)+hstep/(m:ℝ) := by
      dsimp [density,probability,ell,s,hstep]
      field_simp
      ring
    _ ≤ _ := hmain

lemma density_bounds (m : ℕ) (S d t : ℝ) (C P : ℕ) (h : Range m d t C P)
    (hm : 2000000≤ m) (htS : t≤S) (hS3 : S^3≤ m) :
    0≤density m S d t ∧ density m S d t≤1 := by
  obtain ⟨hell,hell1⟩ := efficiency_bounds m hm
  have hell0 : 0≤efficiency m := le_trans (by norm_num) hell
  have hs : 0≤S-t := sub_nonneg.mpr htS
  have hd := h.d_pos
  have hS1 : 1≤S := h.t_one.trans htS
  have hS : S≤d := by
    have hh : S≤S^3 := by simpa only [pow_one] using pow_le_pow_right₀ hS1 (by decide : 1≤3)
    exact hh.trans (hS3.trans h.m_le_d)
  have ht : 0≤t := by have := h.t_one; linarith
  constructor
  · unfold density; positivity
  · unfold density
    apply (div_le_one hd).mpr
    have hh := mul_le_mul_of_nonneg_right hell1 hs
    nlinarith only [hh,hS,ht]

lemma density_pos (m : ℕ) (S d t : ℝ) (hm : 2000000≤ m) (hd : 0<d) (htS : t<S) :
    0<density m S d t := by
  have hell : 0<efficiency m := lt_of_lt_of_le (by norm_num) (efficiency_bounds m hm).1
  exact div_pos (mul_pos hell (sub_pos.mpr htS)) hd

lemma nextD_pos (m : ℕ) (d t : ℝ) (hd : 0<d) : 0<nextD m d t := by
  unfold nextD
  positivity

lemma nextD_le (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) : nextD m d t≤d := by
  have hg := (growth_bounds m t h.large h.t_one).1
  have he : Real.exp (-growth m t)≤1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hg)
  have hh := mul_le_mul_of_nonneg_left he h.d_pos.le
  simpa [nextD,growth,neg_mul] using hh

#print axioms efficiency_bounds
#print axioms next_density
#print axioms future_lower
#print axioms rate_margin
#print axioms density_bounds
#print axioms density_pos
#print axioms nextD_le
end
end Erdos773.GreedyBatchDensityProfile
