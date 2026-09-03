import Submission.GreedyBatchMomentBounds

/-! Uniform shrinking-batch moment bounds under coarse scalar scale
conditions. These conditions do not yet assert any degree trajectory. -/
namespace Erdos773.GreedyBatchScaleTails
open IndexedBernoulliMoments GreedyBatchScalarTails GreedyBatchMomentBounds
set_option maxHeartbeats 3000000
noncomputable section

def u (m : ℕ) : ℝ := 1/(20*(m:ℝ)^2)
def failure (m : ℕ) : ℝ := 2*Real.exp (-(m:ℝ)^7)

lemma u_nonneg (m : ℕ) : 0≤u m := by unfold u; positivity
lemma u_le_quarter (m : ℕ) (hm : 1≤ m) : u m≤1/4 := by
  have hmR : (1:ℝ)≤ m := by exact_mod_cast hm
  have hm2 : (1:ℝ)≤(m:ℝ)^2 := one_le_pow₀ hmR
  unfold u
  apply (div_le_iff₀ (by positivity : (0:ℝ)<20*(m:ℝ)^2)).mpr
  nlinarith only [hm2]

/-- A rank-at-most-four overlap error is negligible at the proposed scale. -/
lemma overlap_error (m r M : ℕ) (hm : 100≤ m) (hr : r≤4) (hM : M≤8*m^2) :
    r*M*(r*m^10+1)^r≤ m^46 := by
  have hm1 : 1≤ m := by omega
  have hm10 : 1≤ m^10 := one_le_pow₀ hm1
  have hh := Nat.mul_le_mul_right (m^10) hr
  have hb : r*m^10+1≤5*m^10 := by omega
  have hp : 0<5*m^10 := by omega
  have hbig : 20000≤ m^4 := by
    have hh := Nat.pow_le_pow_left hm 4
    norm_num at hh
    omega
  calc
    _ ≤ 4*(8*m^2)*(5*m^10)^4 := Nat.mul_le_mul (Nat.mul_le_mul hr hM)
      ((Nat.pow_le_pow_left hb r).trans (Nat.pow_le_pow_right hp hr))
    _ = 20000*m^42 := by ring
    _ ≤ m^4*m^42 := Nat.mul_le_mul_right _ hbig
    _ = _ := by ring

lemma budget_scale (m r q n : ℕ) (K : ℕ → ℕ) (p : ℝ)
    (hm : 100≤ m) (hr : r≤4) (hq : q=m^10)
    (hp : 0≤p) (hp1 : p≤1) (h0 : K 0≤n)
    (hK : ∀ k, 1≤k → k≤r → K k≤8*m^2) :
    budget r q K p≤(n:ℝ)*p^r+(m:ℝ)^46 := by
  subst q
  have hh := budget_uniform r (m^10) n (8*m^2) K p hp hp1 h0 hK
  have he : (r:ℝ)*(8*m^2:ℕ)*((r*m^10+1:ℕ):ℝ)^r≤(m:ℝ)^46 := by
    exact_mod_cast overlap_error m r (8*m^2) hm hr le_rfl
  linarith only [hh,he]

/-- A margin S/m^4 absorbs the overlap error without multiplying the leading
mean by a fixed constant. -/
lemma near_mean_margin (m : ℕ) (S μ : ℝ) (hm : 100≤ m) (hS : (m:ℝ)^52≤S)
    (hμ : μ≤10*S/(m:ℝ)^2) :
    μ+(m:ℝ)^46≤(1-u m)*(μ+S/(m:ℝ)^4) := by
  have hmR : (100:ℝ)≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ)< m := by linarith only [hmR]
  have hm1 : (1:ℝ)≤ m := by linarith only [hmR]
  have hS0 : 0≤S := (pow_nonneg hm0.le 52).trans hS
  have hm2 : (4:ℝ)≤(m:ℝ)^2 := by nlinarith only [hmR]
  have hE : (m:ℝ)^46≤S/(4*(m:ℝ)^4) := by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<4*(m:ℝ)^4)).mpr
    have hh := mul_le_mul_of_nonneg_right hm2 (pow_nonneg hm0.le 50)
    nlinarith only [hh,hS]
  have h42 : (m:ℝ)^2≤(m:ℝ)^4 := pow_le_pow_right₀ hm1 (by decide)
  have hmargin : S/(m:ℝ)^4≤S/(m:ℝ)^2 :=
    div_le_div_of_nonneg_left hS0 (by positivity) h42
  have hL : μ+S/(m:ℝ)^4≤11*S/(m:ℝ)^2 := by
    ring_nf at hμ hmargin ⊢
    linarith only [hμ,hmargin]
  have huL : u m*(μ+S/(m:ℝ)^4)≤11*S/(20*(m:ℝ)^4) := by
    calc
      _ ≤ u m*(11*S/(m:ℝ)^2) := mul_le_mul_of_nonneg_left hL (u_nonneg m)
      _ = _ := by unfold u; field_simp
  have hmarg : 0≤S/(m:ℝ)^4 := div_nonneg hS0 (pow_nonneg hm0.le 4)
  have hE' : (m:ℝ)^46≤(1/4)*(S/(m:ℝ)^4) := by convert hE using 1 <;> ring
  have hU' : u m*(μ+S/(m:ℝ)^4)≤(11/20)*(S/(m:ℝ)^4) := by convert huL using 1 <;> ring
  nlinarith only [hE',hU',hmarg]

lemma loose_margin (m : ℕ) (μ L : ℝ) (hm : 1≤ m) (hL : 0≤L)
    (hμ : μ≤L/4) (hE : (m:ℝ)^46≤L/4) :
    μ+(m:ℝ)^46≤(1-u m)*L := by
  have hh := mul_le_mul_of_nonneg_right (u_le_quarter m hm) hL
  nlinarith only [hμ,hE,hh,hL]

lemma scaled_moment (m r n : ℕ) (K : ℕ → ℕ) (p L : ℝ)
    (hm : 100≤ m) (hr : r≤4) (hp : 0≤p) (hp1 : p≤1) (hL : 0<L)
    (h0 : K 0≤n) (hK : ∀ k, 1≤k → k≤r → K k≤8*m^2)
    (hmargin : (n:ℝ)*p^r+(m:ℝ)^46≤(1-u m)*L) :
    (budget r (m^10) K p/L)^(m^10)≤Real.exp (-(m:ℝ)^7) := by
  have ht := moment_exponential r (m^10) K p L (u m) hp hL (u_nonneg m)
    ((u_le_quarter m (by omega)).trans (by norm_num))
    ((budget_scale m r (m^10) n K p hm hr rfl hp hp1 h0 hK).trans hmargin)
  exact ht.trans (shrinking_scale m (by omega))

/-- Four old-survival tests share this one scalar calculation. The family
mass n is allowed to be a cap rather than an attained cardinality. -/
theorem old_scaled (m n s D M : ℕ) (p : ℝ) (hm : 100≤ m) (hM : 0<M)
    (hn : m^30*M≤n) (hs : s≤3*D) (hp : 0≤p) (hDp : (D:ℝ)*p≤4/(m:ℝ)^2) :
    hitError n s M (m^10) p (1/(m:ℝ)^2) (100*n/(m:ℝ)^4)≤failure m := by
  have hmR : (100:ℝ)≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ)< m := by linarith only [hmR]
  have hm1 : (1:ℝ)≤ m := by linarith only [hmR]
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hnR : (m:ℝ)^30*M≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := (mul_pos (pow_pos hm0 30) hMr).trans_le hnR
  have hL : 0<100*(n:ℝ)/(m:ℝ)^4 := by positivity
  have hsp : (s:ℝ)*p≤12/(m:ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_right (show (s:ℝ)≤3*D by exact_mod_cast hs) hp
    ring_nf at hh hDp ⊢
    nlinarith only [hh,hDp]
  have hterm1 : (n:ℝ)*s^2*p^2/2≤72*n/(m:ℝ)^4 := by
    have h0 : (0:ℝ)≤(s:ℝ)*p := by positivity
    have hh := pow_le_pow_left₀ h0 hsp 2
    have he : (12/(m:ℝ)^2)^2=144/(m:ℝ)^4 := by ring
    rw [he] at hh
    have hm := mul_le_mul_of_nonneg_left hh hn0.le
    ring_nf at hm ⊢
    linarith only [hm]
  have hterm2 : 2*((m^10:ℕ):ℝ)*s*M*p≤24*(m:ℝ)^8*M := by
    have hh := mul_le_mul_of_nonneg_left hsp (show (0:ℝ)≤2*(m:ℝ)^10*M by positivity)
    have he : 2*(m:ℝ)^10*M*(12/(m:ℝ)^2)=24*(m:ℝ)^8*M := by field_simp; norm_num
    rw [he] at hh
    push_cast
    nlinarith only [hh]
  have hp820 : (m:ℝ)^8≤(m:ℝ)^20 := pow_le_pow_right₀ hm1 (by decide)
  have htwos : 2*((m^10:ℕ):ℝ)*s*M*p+2*(((m^10:ℕ):ℝ))^2*M≤26*(m:ℝ)^20*M := by
    have hh := mul_le_mul_of_nonneg_right hp820 hMr.le
    push_cast at hterm2 ⊢
    nlinarith only [hterm2,hh]
  have hsmall : 26*(m:ℝ)^20*M≤(n:ℝ)/(m:ℝ)^4 := by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<(m:ℝ)^4)).mpr
    have hm6 : (26:ℝ)≤(m:ℝ)^6 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤100) hmR 6
      norm_num at hh
      linarith only [hh]
    have hh := mul_le_mul_of_nonneg_right hm6 (show (0:ℝ)≤(m:ℝ)^24*M by positivity)
    nlinarith only [hh,hnR]
  have hbudget : budget 2 (m^10) (BernoulliHitCounts.overlapCaps n s M) p≤
      (1-u m)*(100*n/(m:ℝ)^4) := by
    have hh := hit_budget n s M (m^10) p hp
    have hu := mul_le_mul_of_nonneg_right (u_le_quarter m (by omega)) hL.le
    ring_nf at hh hterm1 htwos hsmall hu hL ⊢
    nlinarith only [hh,hterm1,htwos,hsmall,hu,hL]
  have hexp : ((m^10:ℕ):ℝ)*u m≤(1/(m:ℝ)^2)^2*(100*n/(m:ℝ)^4)/(2*M) := by
    have hpow : (m:ℝ)^16≤(m:ℝ)^30 := pow_le_pow_right₀ hm1 (by decide)
    have hh := mul_le_mul_of_nonneg_right hpow hMr.le
    have hbound : M*(m:ℝ)^16≤1000*(n:ℝ) := by nlinarith only [hh,hnR,hn0]
    have heL : ((m^10:ℕ):ℝ)*u m=(m:ℝ)^8/20 := by
      unfold u
      push_cast
      field_simp
    have heR : (1/(m:ℝ)^2)^2*(100*n/(m:ℝ)^4)/(2*M)=50*n/(M*(m:ℝ)^8) := by
      field_simp
      ring
    rw [heL,heR]
    apply (le_div_iff₀ (by positivity : (0:ℝ)<M*(m:ℝ)^8)).mpr
    nlinarith only [hbound]
  have ht := hit_exponential n s M (m^10) p (1/(m:ℝ)^2) (100*n/(m:ℝ)^4) (u m)
    hp hL (u_nonneg m) ((u_le_quarter m (by omega)).trans (by norm_num)) hexp hbudget
  exact ht.trans (mul_le_mul_of_nonneg_left (shrinking_scale m (by omega)) (by norm_num))

#print axioms overlap_error
#print axioms budget_scale
#print axioms near_mean_margin
#print axioms scaled_moment
#print axioms old_scaled
end
end Erdos773.GreedyBatchScaleTails
