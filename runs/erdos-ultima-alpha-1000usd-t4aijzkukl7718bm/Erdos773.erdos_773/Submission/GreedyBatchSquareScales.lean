import Submission.GreedyBatchSquareCertificate

/-! Explicit scalar parameters for applying the shrinking-batch theorem to
squares. These lemmas address the two-thirds coefficient only. -/
namespace Erdos773.GreedyBatchSquareScales
open Filter GreedyBatchDensityProfile GreedyBatchProfileStep GreedyBatchVolume
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section

def exponent : ℕ := 1000000000
def eta : ℝ := 1/1000000000
def kappa : ℝ := 1999/6000
def c : ℝ := 19999/60000
def loss : ℝ := 99999/100000
def smallDelta : ℝ := 1/240000

def root (X : ℝ) : ℕ := ⌈X^eta⌉₊
def scale (X : ℝ) : ℝ := (kappa*X/(Real.log X)^2)^(1/3:ℝ)
def horizon (X : ℝ) : ℝ := (c*Real.log X)^(1/3:ℝ)

lemma scale_pos {X : ℝ} (hX : 0<X) (hL : 0<Real.log X) : 0<scale X := by
  apply Real.rpow_pos_of_pos
  dsimp [kappa]
  positivity

lemma scale_cube {X : ℝ} (hX : 0≤X) : (scale X)^3=kappa*X/(Real.log X)^2 := by
  unfold scale
  rw [← Real.rpow_mul_natCast (by dsimp [kappa]; positivity : 0≤kappa*X/(Real.log X)^2)]
  norm_num

lemma horizon_pos {X : ℝ} (hL : 0<Real.log X) : 0<horizon X := by
  apply Real.rpow_pos_of_pos
  dsimp [c]
  positivity

lemma horizon_cube {X : ℝ} (hL : 0≤Real.log X) : (horizon X)^3=c*Real.log X := by
  unfold horizon
  rw [← Real.rpow_mul_natCast (by dsimp [c]; positivity : 0≤c*Real.log X)]
  norm_num

lemma root_lower (X : ℝ) : X^eta≤(root X:ℝ) := Nat.le_ceil _

lemma volume {X : ℝ} (hX : 0≤X) : X≤(root X:ℝ)^exponent := by
  have hh := pow_le_pow_left₀ (Real.rpow_nonneg hX eta) (root_lower X) exponent
  rw [← Real.rpow_mul_natCast hX] at hh
  norm_num [eta,exponent] at hh
  exact hh

lemma root_upper {X : ℝ} (hX : 0≤X) (htwo : 2≤X^eta) : (root X:ℝ)≤X^(2*eta) := by
  have hc := (Nat.ceil_lt_add_one (Real.rpow_nonneg hX eta)).le
  have hs : X^eta+1≤(X^eta)^2 := by nlinarith only [htwo]
  have hh := hc.trans hs
  rw [← Real.rpow_mul_natCast hX] at hh
  simpa only [root,Nat.cast_ofNat,mul_comm eta (2:ℝ)] using hh

lemma horizon_large {X : ℝ} (hL : (4000000000000000000:ℝ)≤Real.log X) : 1000000≤horizon X := by
  have hL0 : 0<Real.log X := by linarith only [hL]
  have hc := horizon_cube hL0.le
  apply le_of_pow_le_pow_left₀ (by decide : 3≠0) (horizon_pos hL0).le
  rw [hc]
  dsimp [c]
  nlinarith only [hL]

lemma horizon_shift {X : ℝ} (hL : (4000000000000000000:ℝ)≤Real.log X) :
    (horizon X+1)^3-1≤(c+smallDelta)*Real.log X := by
  have hL0 : 0<Real.log X := by linarith only [hL]
  have ht := horizon_large hL
  have ht0 := horizon_pos hL0
  have hsq : horizon X≤(horizon X)^2 := by nlinarith only [ht]
  have hmul := mul_le_mul_of_nonneg_right ht (sq_nonneg (horizon X))
  have hc := horizon_cube hL0.le
  have hdelta : 6*(horizon X)^2≤smallDelta*Real.log X := by
    dsimp [c,smallDelta] at hc ⊢
    nlinarith only [hmul,hc,hL0.le]
  nlinarith only [hsq,hc,hdelta]

lemma scale_upper {X : ℝ} (hX : 1≤X) (hL : 1≤Real.log X) : scale X≤X := by
  have hsq : 1≤(Real.log X)^2 := one_le_pow₀ hL
  have hscale : (scale X)^3≤X := by
    rw [scale_cube (by linarith only [hX])]
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hsq (by linarith only [hX] : 0≤X)
    dsimp [kappa]
    linarith only [hh,hX]
  have hpow : X≤X^3 := by simpa using pow_le_pow_right₀ hX (by decide : 1≤3)
  exact le_of_pow_le_pow_left₀ (by decide : 3≠0) (by linarith only [hX]) (hscale.trans hpow)

lemma scale_lower {X : ℝ} (hX : 0<X) (hL : 0<Real.log X)
    (hs : Real.log X≤(1/2:ℝ)*X^(1/160000:ℝ)) : X^(1/3-smallDelta)≤scale X := by
  have hs2 := pow_le_pow_left₀ hL.le hs 2
  rw [mul_pow,← Real.rpow_mul_natCast hX.le] at hs2
  have hsq : (Real.log X)^2≤kappa*X^(3*smallDelta) := by
    norm_num [kappa,smallDelta] at hs2 ⊢
    have hh := Real.rpow_nonneg hX.le (1/80000:ℝ)
    linarith only [hs2,hh]
  have hp : X^(1-3*smallDelta)*X^(3*smallDelta)=X := by
    rw [← Real.rpow_add hX]
    norm_num
  have hm := mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hX.le (1-3*smallDelta))
  have hc : X^(1-3*smallDelta)≤kappa*X/(Real.log X)^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
    calc
      _ ≤ X^(1-3*smallDelta)*(kappa*X^(3*smallDelta)) := hm
      _ = kappa*X := by rw [← mul_assoc,mul_comm _ kappa,mul_assoc,hp]
  apply le_of_pow_le_pow_left₀ (by decide : 3≠0) (scale_pos hX hL).le
  rw [scale_cube hX.le,← Real.rpow_mul_natCast hX.le]
  convert hc using 1 <;> congr 1 <;> ring

lemma terminal {X : ℝ} (hX : 1≤X) (hm : 2000000≤root X)
    (hL : (4000000000000000000:ℝ)≤Real.log X) (htwo : 2≤X^eta)
    (hs : Real.log X≤(1/2:ℝ)*X^(1/160000:ℝ)) :
    (root X:ℝ)^1000≤scale X*Real.exp (-a (root X)*((horizon X+1)^3-1)) := by
  have hX0 : 0<X := by linarith only [hX]
  have hL0 : 0<Real.log X := by linarith only [hL]
  have hscale := scale_lower hX0 hL0 hs
  have hshift := horizon_shift hL
  have hT := horizon_large hL
  have hE : 0≤(horizon X+1)^3-1 := sub_nonneg.mpr (one_le_pow₀ (by linarith only [hT]))
  have ha : a (root X)≤1 := (coefficients (root X) (by omega)).2.2.2.2.1
  have hpen : a (root X)*((horizon X+1)^3-1)≤(c+smallDelta)*Real.log X :=
    (mul_le_mul_of_nonneg_right ha hE).trans (by simpa using hshift)
  have he : X^(-(c+smallDelta))≤Real.exp (-a (root X)*((horizon X+1)^3-1)) := by
    rw [Real.rpow_def_of_pos hX0]
    apply Real.exp_le_exp.mpr
    nlinarith only [hpen]
  have hprod := mul_le_mul hscale he (Real.rpow_nonneg hX0.le _) (scale_pos hX0 hL0).le
  rw [← Real.rpow_add hX0] at hprod
  have hid : (1/3-smallDelta)+-(c+smallDelta)=(1/120000:ℝ) := by norm_num [smallDelta,c]
  rw [hid] at hprod
  have hroot := pow_le_pow_left₀ (Nat.cast_nonneg (root X)) (root_upper hX0.le htwo) 1000
  rw [← Real.rpow_mul_natCast hX0.le] at hroot
  exact hroot.trans ((Real.rpow_le_rpow_of_exponent_le hX (by norm_num [eta])).trans hprod)

lemma efficiency_lower (m : ℕ) (hm : 100000000000≤ m) : loss≤efficiency m := by
  have hmR : (100000000000:ℝ)≤ m := by exact_mod_cast hm
  have hh : (1000000:ℝ)/(m:ℝ)≤1/100000 := (div_le_iff₀ (by linarith only [hmR])).mpr (by linarith only [hmR])
  dsimp [loss,efficiency]
  linarith only [hh]

/-- The tiny coefficient gain is kept explicitly, instead of discarded as
an unspecified constant. -/
lemma coefficient {X V : ℝ} {m : ℕ} (hX : 0<X)
    (hL : (4000000000000000000:ℝ)≤Real.log X) (hm : 100000000000≤ m)
    (hV : loss*X/Real.log X≤V) :
    X^(2/3:ℝ)≤efficiency m*(horizon X-1)/scale X*V := by
  have hL0 : 0<Real.log X := by linarith only [hL]
  have hd := scale_pos hX hL0
  have hT := horizon_large hL
  have ht : 0<horizon X := horizon_pos hL0
  have htime : loss*horizon X≤horizon X-1 := by dsimp [loss]; linarith only [hT]
  have hl : (0:ℝ)≤loss := by norm_num [loss]
  have he := efficiency_lower m hm
  have hV0 : 0≤V := le_trans (by positivity) hV
  have hh := mul_le_mul he htime (by positivity : 0≤loss*horizon X) (hl.trans he)
  have htm : 0≤horizon X-1 := by linarith only [hT]
  have hh' := mul_le_mul (div_le_div_of_nonneg_right hh hd.le) hV (by positivity : 0≤loss*X/Real.log X)
    (by have := hl.trans he; positivity : 0≤efficiency m*(horizon X-1)/scale X)
  let w : ℝ := loss^3*horizon X*X/(scale X*Real.log X)
  have hw : w≤efficiency m*(horizon X-1)/scale X*V := by
    convert hh' using 1 <;> dsimp [w] <;> ring
  have hw0 : 0≤w := by dsimp [w]; positivity
  have hw3 : w^3=(loss^9*c/kappa)*X^2 := by
    dsimp [w]
    simp only [div_pow,mul_pow]
    rw [horizon_cube hL0.le,scale_cube hX.le]
    have hk : kappa≠0 := by norm_num [kappa]
    field_simp [hX.ne',hL0.ne',hk]
    <;> ring
  have hconst : (1:ℝ)≤loss^9*c/kappa := by norm_num [loss,c,kappa]
  have hr : (X^(2/3:ℝ))^3=X^2 := by
    rw [← Real.rpow_mul_natCast hX.le]
    norm_num
  have hc := mul_le_mul_of_nonneg_right hconst (sq_nonneg X)
  have hlow : X^(2/3:ℝ)≤w := by
    apply le_of_pow_le_pow_left₀ (by decide : 3≠0) hw0
    rw [hr,hw3]
    simpa only [one_mul] using hc
  exact hlow.trans hw

#print axioms volume
#print axioms scale_lower
#print axioms terminal
#print axioms coefficient
end
end Erdos773.GreedyBatchSquareScales
