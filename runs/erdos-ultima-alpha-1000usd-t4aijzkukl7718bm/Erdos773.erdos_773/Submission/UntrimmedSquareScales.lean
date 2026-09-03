import Submission.RelaxedSquareLower

/-! Numerical conversion for the untrimmed square-root carrier. -/
namespace Erdos773.UntrimmedSquareScales
open Finset Filter GreedyCodegreeSquareScales RelaxedSquareLower RefinedSquareLower
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
noncomputable section

def root (X L : ℝ) : ℕ := degreeRoot (X/4) L

lemma root_degree {X L : ℝ} (hX : 0 ≤ X) : (1/3:ℝ)*X/L^2 ≤ (root X L:ℝ)^300 := by
  have hh := root_lower (X := X/4) (L := L) (by positivity)
  have he : degreeScale (X/4) L=(1/3:ℝ)*X/L^2 := by unfold degreeScale; ring
  rwa [he] at hh

lemma volume {X L : ℝ} (hX : 1 ≤ X) (hL : 0<L) (hlog : 3*L^2 ≤ X^(1/301:ℝ)) :
    X ≤ (root X L:ℝ)^301 := by
  have hX0 : 0<X := by linarith only [hX]
  have hz : 0 ≤ X^(300/301:ℝ) := Real.rpow_nonneg hX0.le _
  have hprod : X^(300/301:ℝ)*X^(1/301:ℝ)=X := by rw [← Real.rpow_add hX0]; norm_num
  have hD : X^(300/301:ℝ) ≤ (1/3:ℝ)*X/L^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
    have hh := mul_le_mul_of_nonneg_left hlog hz
    rw [hprod] at hh
    nlinarith only [hh]
  have hv := pow_le_pow_left₀ hz (hD.trans (root_degree hX0.le)) 301
  have he : (X^(300/301:ℝ))^301=X^300 := by
    rw [← Real.rpow_mul_natCast hX0.le]
    norm_num
  rw [he] at hv
  apply le_of_pow_le_pow_left₀ (by decide : (300:ℕ) ≠ 0) (by positivity : 0 ≤ (root X L:ℝ)^301)
  simpa only [← pow_mul,show (300:ℕ)*301=301*300 by omega] using hv

lemma root_upper {X L : ℝ} (hX : 0 ≤ X) (hL : 0<L) (hm : 1000001 ≤ root X L) :
    (root X L:ℝ)^300*L^2 ≤ (667/2000:ℝ)*X := by
  have hh := refined_root_upper (X := X/4) (L := L) (by positivity) hL hm
  convert hh using 1; ring

lemma scale_lower {X L a M : ℝ} {n : ℕ} (hX : 0<X) (hL : 0<L) (hn : 0<n)
    (ha : (999/1000:ℝ)*X/L ≤ a)
    (hdegree : (n:ℝ)^300*L^2 ≤ (667/2000:ℝ)*X)
    (hM : longHorizon L*a/((100/99:ℝ)*(n:ℝ)^100) ≤ M) :
    (1/36:ℝ)*X^(2/3:ℝ) ≤ M := by
  let R : ℝ := (X*L)^(1/3:ℝ)
  have hR : 0<R := Real.rpow_pos_of_pos (mul_pos hX hL) _
  have hR3 : R^3=X*L := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast (mul_nonneg hX.le hL.le)]
    norm_num
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hτ : 0 ≤ longHorizon L := by unfold longHorizon; positivity
  have hcube : ((n:ℝ)^100*L)^3 ≤ (667/2000:ℝ)*X*L := by
    have hh := mul_le_mul_of_nonneg_right hdegree hL.le
    nlinarith only [hh]
  have hden : (100000/98901:ℝ)*(n:ℝ)^100*L ≤ (18/25:ℝ)*R := by
    have hh : (n:ℝ)^100*L ≤ (890109/1250000:ℝ)*R := by
      apply le_of_pow_le_pow_left₀ (by decide : (3:ℕ) ≠ 0) (by positivity : 0 ≤ (890109/1250000:ℝ)*R)
      rw [show ((890109/1250000:ℝ)*R)^3=(890109/1250000:ℝ)^3*(X*L) by rw [mul_pow,hR3]]
      nlinarith only [hcube,mul_nonneg hX.le hL.le]
    linarith only [hh]
  have hsmall := div_le_div_of_nonneg_left (show 0 ≤ longHorizon L*X by positivity)
    (by positivity : 0<(100000/98901:ℝ)*(n:ℝ)^100*L) hden
  have hsize := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ha hτ)
    (by positivity : 0 ≤ (100/99:ℝ)*(n:ℝ)^100)
  have he : longHorizon L*((999/1000:ℝ)*X/L)/((100/99:ℝ)*(n:ℝ)^100)=
      longHorizon L*X/((100000/98901:ℝ)*(n:ℝ)^100*L) := by ring
  rw [he] at hsize
  have hid : longHorizon L*X/((18/25:ℝ)*R)=(1/36:ℝ)*X^(2/3:ℝ) := by
    have hx : 0<X^(1/3:ℝ) := Real.rpow_pos_of_pos hX _
    have hl : 0<L^(1/3:ℝ) := Real.rpow_pos_of_pos hL _
    have hxsum : X^(1/3:ℝ)*X^(2/3:ℝ)=X := by rw [← Real.rpow_add hX]; norm_num
    dsimp [longHorizon,R]
    rw [Real.mul_rpow hX.le hL.le]
    field_simp
    nlinarith only [hxsum]
  rw [← hid]
  exact hsmall.trans (hsize.trans hM)

#print axioms root_degree
#print axioms volume
#print axioms root_upper
#print axioms scale_lower
end
end Erdos773.UntrimmedSquareScales
