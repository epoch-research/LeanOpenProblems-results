import Submission.GreedyBatchFutureProfiles

/-! Complete deterministic Fits verification for the actual ceiling profiles. -/
namespace Erdos773.GreedyBatchProfileFits
open GreedyBatchProfiles GreedyBatchProfileStep GreedyBatchProfileConditions
open GreedyBatchCertificate GreedyBatchScaledErrors GreedyBatchScalarTails
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section

lemma profile_large (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    3*(m:ℝ)^4≤f2 m d t ∧ 3*(m:ℝ)^4≤f3 m d t ∧
    3*(m:ℝ)^4≤f4 d ∧ 3*(m:ℝ)^4≤fb m d := by
  have hm := h.m_pos.le
  have hd := h.d_pos.le
  have hd1 : 1≤d := by have := h.d_large; linarith
  have ht := h.t_one
  have hdt := mul_le_mul_of_nonneg_left (one_le_pow₀ (n := 2) ht) hd
  have hdt3 := mul_le_mul_of_nonneg_left ht (sq_nonneg d)
  have hd2 : d≤d^2 := by nlinarith only [hd1]
  have hd3 : d≤d^3 := by simpa only [pow_one] using pow_le_pow_right₀ hd1 (by decide : 1≤3)
  have hmd := mul_le_mul_of_nonneg_right (one_le_pow₀ (n := 50) h.m_one) hd
  have hc := coefficients m h.large
  have hA := mul_le_mul_of_nonneg_right (hc.1.trans hc.2.1) (show 0≤d*t^2 by positivity)
  have ht0 : 0≤t := by linarith only [ht]
  have hB := mul_le_mul_of_nonneg_right hc.1 (show 0≤d^2*t by positivity)
  have hsmall : 3*(m:ℝ)^4≤d :=
    (power_slack m 4 5 3 h.large (by norm_num) (by decide)).trans (h.power_le_d 5 (by decide))
  dsimp [f2,f3,f4,fb]
  exact ⟨by nlinarith only [hsmall,hA,hdt,hd],by nlinarith only [hsmall,hB,hdt3,hd2,sq_nonneg d],
    hsmall.trans hd3,by nlinarith only [hsmall,hmd]⟩

/-- Every old killing-set deficit is negligible at the large-d scale. -/
lemma deficit_bound (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    probability m d t*(3*(C+1):ℕ)≤1/(2*(m:ℝ)^4) := by
  have hm := h.m_pos
  have hp := (probability_pos m d t C P h).le
  have hC : (C:ℝ)≤(m:ℝ)^60 := by exact_mod_cast h.common
  have hpow : (1:ℝ)≤(m:ℝ)^60 := one_le_pow₀ h.m_one
  have hC1 : (C:ℝ)+1≤2*(m:ℝ)^60 := by linarith only [hC,hpow]
  have hh := mul_le_mul_of_nonneg_right hC1 (show 0≤6*(m:ℝ)^2 by positivity)
  have hslack : 12*(m:ℝ)^62≤d :=
    (power_slack m 62 63 12 h.large (by norm_num) (by decide)).trans (h.power_le_d 63 (by decide))
  have hsmall : 6*((C:ℝ)+1)*(m:ℝ)^2≤d := by nlinarith only [hh,hslack]
  have hp' := mul_le_mul_of_nonneg_right hsmall hp
  have hpd := probability_mul m d t (ne_of_gt h.d_pos)
  have hstep : step m t*(m:ℝ)^2≤1 :=
    (le_div_iff₀ (by positivity)).mp (step_bound m t (by have := h.large; omega))
  have hp'' := mul_le_mul_of_nonneg_right hp' (sq_nonneg (m:ℝ))
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2*(m:ℝ)^4)).mpr
  push_cast
  have he : d*probability m d t*(m:ℝ)^2=step m t*(m:ℝ)^2 := by rw [mul_comm d,hpd]
  rw [he] at hp''
  nlinarith only [hp'',hstep]

lemma ceil_small (m : ℕ) (F : ℝ) (hm : 1≤ m) (hF : 3*(m:ℝ)^4≤F) :
    0≤F ∧ (⌈F⌉₊:ℝ)≤F+1 ∧ (⌈F⌉₊:ℝ)≤2*F ∧ 3≤F/(m:ℝ)^4 := by
  have hm1 : (1:ℝ)≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ)< m := by linarith only [hm1]
  have hpow : (1:ℝ)≤(m:ℝ)^4 := one_le_pow₀ hm1
  have hF0 : 0≤F := by nlinarith only [hF,hpow]
  have hc := (ceil_bounds F hF0).2
  exact ⟨hF0,hc,by linarith only [hc,hF,hpow],(le_div_iff₀ (by positivity)).mpr (by linarith only [hF])⟩

lemma old_bound (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P)
    (F : ℝ) (hF : 3*(m:ℝ)^4≤F) (k e : ℕ) (hk : k≤3) (he : e≤3*(C+1)) :
    (⌈F⌉₊:ℝ)*(1-(1-1/(m:ℝ)^2)*probability m d t*((k*(caps m d t C P).D2:ℕ)-(e:ℕ):ℝ))+
      100*(⌈F⌉₊:ℝ)/(m:ℝ)^4≤
      F*(1-(1-1/(m:ℝ)^2)*probability m d t*k*f2 m d t)+202*F/(m:ℝ)^4 := by
  obtain ⟨hF0,hceil,hceil2,hround⟩ := ceil_small m F (by have := h.large; omega) hF
  have hm := h.m_pos
  have hp := (probability_pos m d t C P h).le
  have hprob := probability_range _ m _ d (conditions m d t C P h)
  have hgl := graph_load m d t C P h
  have hkR : (k:ℝ)≤3 := by exact_mod_cast hk
  have hload : (k:ℝ)*(caps m d t C P).D2*probability m d t≤1 := by
    have hh := mul_le_mul_of_nonneg_right hkR
      (show 0≤((caps m d t C P).D2:ℝ)*probability m d t by positivity)
    have hmR : (100:ℝ)≤ m := by exact_mod_cast h.large
    have h12 : (12:ℝ)/(m:ℝ)^2≤1 := (div_le_one (by positivity)).mpr (by nlinarith only [hmR])
    ring_nf at hh hgl h12 ⊢
    nlinarith only [hh,hgl,h12]
  have hdef : probability m d t*(e:ℝ)≤(1/(m:ℝ)^4)/2 := by
    have hh := mul_le_mul_of_nonneg_left (show (e:ℝ)≤(3*(C+1):ℕ) by exact_mod_cast he) hp
    have hd := deficit_bound m d t C P h
    convert hh.trans hd using 1 <;> ring
  have ht := GreedyBatchCeilingErrors.old_upper (⌈F⌉₊:ℝ) F (caps m d t C P).D2 (f2 m d t)
    k e (probability m d t) (1/(m:ℝ)^2) (1/(m:ℝ)^4)
    (Nat.cast_nonneg _) hF0 (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hp
    hprob.eta_nonneg hprob.eta_le_one (by positivity) hceil hceil2
    (by ring_nf at hround ⊢; linarith only [hround]) (Nat.le_ceil _) hload hdef
  convert ht using 1 <;> push_cast <;> ring

lemma promotion_bound (m : ℕ) (F S w : ℝ) (hm : 1≤ m) (hF : 0≤F) (hS : 3*(m:ℝ)^4≤S)
    (hw : 0≤w) (hw3 : w≤3) :
    w*(⌈F⌉₊:ℝ)+(⌈S⌉₊:ℝ)/(m:ℝ)^4≤w*F+3*S/(m:ℝ)^4 := by
  obtain ⟨hS0,hceil,hceil2,hround⟩ := ceil_small m S hm hS
  have hsource := (ceil_bounds F hF).2
  have hh := GreedyBatchCeilingErrors.promotion_upper (⌈F⌉₊:ℝ) F (⌈S⌉₊:ℝ) S w (1/(m:ℝ)^4)
    hw (by positivity) hsource hceil2 (by ring_nf at hround ⊢; linarith only [hw3,hround])
  convert hh using 1 <;> ring

lemma shared_margin (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    (m:ℝ)*d≤fb m d/(m:ℝ)^4 := by
  have hm := h.m_pos
  have hd := h.d_pos.le
  have hp : (m:ℝ)≤(m:ℝ)^46 := by simpa only [pow_one] using pow_le_pow_right₀ h.m_one (by decide : 1≤46)
  have hh := mul_le_mul_of_nonneg_right hp hd
  have he : fb m d/(m:ℝ)^4=(m:ℝ)^46*d := by unfold fb; field_simp
  rwa [he]

/-- Every deterministic target inequality holds for the next ceiling
profiles. This does not assert that the next d is still above m^1000. -/
theorem fits (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    Fits (caps m d t C P) (margins (caps m d t C P) m (probability m d t) d)
      (probability m d t) (1/(m:ℝ)^2)
      (caps m (nextD m d t) (t+step m t) (C+4*m^52) P) := by
  have hm := h.m_pos
  have hp := (probability_pos m d t C P h).le
  have hp1 := probability_le_one m d t C P h
  have hp2 := pow_le_one₀ hp hp1 (n := 2)
  obtain ⟨hF2,hF3,hF4,hFB⟩ := profile_large m d t C P h
  obtain ⟨hpos2,hpos3,hpos4,hposB⟩ := profile_positive m d t C P h
  have ho2 := old_bound m d t C P h (f2 m d t) hF2 1 1 (by decide) (by omega)
  have ho3 := old_bound m d t C P h (f3 m d t) hF3 2 (2+C) (by decide) (by omega)
  have ho4 := old_bound m d t C P h (f4 d) hF4 3 (3+3*C) (by decide) (by omega)
  have hoB := old_bound m d t C P h (fb m d) hFB 2 (2+C) (by decide) (by omega)
  have hp31 := promotion_bound m (f3 m d t) (f2 m d t) (2*probability m d t)
    (by have := h.large; omega) hpos3.le hF2 (by positivity) (by linarith only [hp1])
  have hp41 := promotion_bound m (f4 d) (f3 m d t) (3*probability m d t)
    (by have := h.large; omega) hpos4.le hF3 (by positivity) (by linarith only [hp1])
  have hp42 := promotion_bound m (f4 d) (f2 m d t) (3*(probability m d t)^2)
    (by have := h.large; omega) hpos4.le hF2 (by positivity) (by linarith only [hp2])
  have hnext2 := (GreedyBatchFutureProfiles.two m d t C P h).trans (Nat.le_ceil _)
  have hnext3 := (GreedyBatchFutureProfiles.three m d t C P h).trans (Nat.le_ceil _)
  have hnext4 := (GreedyBatchFutureProfiles.four m d t C P h).trans (Nat.le_ceil _)
  have hnextB := (GreedyBatchFutureProfiles.shared m d t C P h).trans (Nat.le_ceil _)
  have hmargin := shared_margin m d t C P h
  have hn2 : 0≤f2 m d t/(m:ℝ)^4 := by positivity
  have hn3 : 0≤f3 m d t/(m:ℝ)^4 := by positivity
  have hn4 : 0≤f4 d/(m:ℝ)^4 := by positivity
  have hnB : 0≤fb m d/(m:ℝ)^4 := by positivity
  dsimp only [caps] at ho2 ho3 ho4 hoB
  constructor
  · dsimp [margins,caps,Caps.degree,retention]
    norm_num at ho2 ⊢
    ring_nf at ho2 hp31 hp42 hnext2 hn2 ⊢
    nlinarith only [ho2,hp31,hp42,hnext2,hn2]
  · dsimp [margins,caps,Caps.degree,retention]
    norm_num at ho3 ⊢
    ring_nf at ho3 hp41 hnext3 hn3 ⊢
    nlinarith only [ho3,hp41,hnext3,hn3]
  · dsimp [margins,caps,Caps.degree,retention]
    norm_num at ho4 ⊢
    ring_nf at ho4 hnext4 hn4 ⊢
    nlinarith only [ho4,hnext4,hn4]
  · dsimp [margins,caps,Caps.degree,retention]
    norm_num at hoB ⊢
    ring_nf at hoB hnextB hmargin hnB ⊢
    nlinarith only [hoB,hnextB,hmargin,hnB]
  · dsimp [margins,caps]
    have hI : Finset.Icc 1 4=({1,2,3,4}:Finset ℕ) := by decide
    rw [hI]
    simp

#print axioms profile_large
#print axioms deficit_bound
#print axioms old_bound
#print axioms promotion_bound
#print axioms fits
end
end Erdos773.GreedyBatchProfileFits
