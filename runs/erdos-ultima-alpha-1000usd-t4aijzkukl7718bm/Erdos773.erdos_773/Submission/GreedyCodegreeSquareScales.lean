import Submission.GreedyCodegreeSquareCertificate
import Submission.GreedyTightSquareScales

/-! Direct square-collision scales without linearizing thinning. -/
namespace Erdos773.GreedyCodegreeSquareScales
open Finset Filter GreedyHorizonFactors
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024
noncomputable section

def degreeScale (X L : ℝ) : ℝ := (4/3:ℝ)*X/L^2
def degreeRoot (X L : ℝ) : ℕ := ⌈(degreeScale X L)^(1/300:ℝ)⌉₊
def horizon (L : ℝ) : ℝ := L^(1/3:ℝ)/160

lemma root_lower {X L : ℝ} (hX : 0 ≤ X) : degreeScale X L ≤ (degreeRoot X L:ℝ)^300 := by
  have hD : 0 ≤ degreeScale X L := by unfold degreeScale; positivity
  have hh := pow_le_pow_left₀ (Real.rpow_nonneg hD (1/300)) (Nat.le_ceil ((degreeScale X L)^(1/300:ℝ))) 300
  have he : ((degreeScale X L)^(1/300:ℝ))^300 = degreeScale X L := by
    rw [← Real.rpow_mul_natCast hD]
    norm_num
  rwa [he] at hh

lemma volume301 {X L : ℝ} (hX : 1 ≤ X) (hL : 0 < L) (hlog : L^2 ≤ X^(1/301:ℝ)) :
    X ≤ (degreeRoot X L:ℝ)^301 := by
  have hX0 : 0 < X := by linarith only [hX]
  have hz : 0 ≤ X^(300/301:ℝ) := Real.rpow_nonneg hX0.le _
  have hprod : X^(300/301:ℝ)*X^(1/301:ℝ) = X := by
    rw [← Real.rpow_add hX0]
    norm_num
  have hDs : X^(300/301:ℝ) ≤ degreeScale X L := by
    apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
    have hh := mul_le_mul_of_nonneg_left hlog hz
    rw [hprod] at hh
    linarith only [hh,hX0.le]
  have hv := pow_le_pow_left₀ hz (hDs.trans (root_lower hX0.le)) 301
  have hz301 : (X^(300/301:ℝ))^301 = X^300 := by
    rw [← Real.rpow_mul_natCast hX0.le]
    norm_num
  rw [hz301] at hv
  apply le_of_pow_le_pow_left₀ (by decide : (300:ℕ) ≠ 0) (by positivity : 0 ≤ (degreeRoot X L:ℝ)^301)
  simpa only [← pow_mul,show (300:ℕ)*301=301*300 by omega] using hv

lemma root_upper {X L : ℝ} (hX : 0 ≤ X) (hL : 0 < L) (hm : 10001 ≤ degreeRoot X L) :
    (degreeRoot X L:ℝ)^300*L^2 ≤ (8/5:ℝ)*X := by
  have hD : 0 ≤ degreeScale X L := by unfold degreeScale; positivity
  have hr := Real.rpow_nonneg hD (1/300:ℝ)
  have hceil := Nat.ceil_lt_add_one hr
  have hmR : (10001:ℝ) ≤ ⌈(degreeScale X L)^(1/300:ℝ)⌉₊ := by exact_mod_cast hm
  have hlarge : 10000 ≤ (degreeScale X L)^(1/300:ℝ) := by linarith only [hceil,hmR]
  have hhi : (degreeRoot X L:ℝ) ≤ (10001/10000:ℝ)*(degreeScale X L)^(1/300:ℝ) := by
    change (⌈(degreeScale X L)^(1/300:ℝ)⌉₊:ℝ) ≤ _
    linarith only [hceil,hlarge]
  have he : ((degreeScale X L)^(1/300:ℝ))^300 = degreeScale X L := by
    rw [← Real.rpow_mul_natCast hD]
    norm_num
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg _) hhi 300
  rw [mul_pow,he] at hp
  have hc : (10001/10000:ℝ)^300 ≤ 6/5 := by norm_num
  have hup := hp.trans (mul_le_mul_of_nonneg_right hc hD)
  have hh := mul_le_mul_of_nonneg_right hup (sq_nonneg L)
  have hid : ((6/5:ℝ)*degreeScale X L)*L^2 = (8/5:ℝ)*X := by unfold degreeScale; field_simp; ring
  rwa [hid] at hh

lemma trim_surplus {X L a E : ℝ} (hX : 0 < X) (hL : 0 < L)
    (ha : (999/1000:ℝ)*X/L ≤ a) (hE : E ≤ (83/1000:ℝ)*X^2/L^3) :
    (3/4:ℝ)*X/L ≤ a-4*E/degreeScale X L := by
  have hD : 0 < degreeScale X L := by unfold degreeScale; positivity
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by norm_num : (0:ℝ) ≤ 4)) hD.le
  have he : 4*((83/1000:ℝ)*X^2/L^3)/degreeScale X L = (249/1000:ℝ)*X/L := by
    unfold degreeScale
    field_simp
    ring
  rw [he] at hh
  calc
    _ = (999/1000:ℝ)*X/L-(249/1000:ℝ)*X/L := by ring
    _ ≤ _ := sub_le_sub ha hh

lemma horizon_cube {L : ℝ} (hL : 0 ≤ L) : (horizon L)^3 = L/4096000 := by
  unfold horizon
  rw [div_pow,← Real.rpow_mul_natCast hL]
  norm_num

lemma horizon_ten {L : ℝ} (hL : 1000000000000 ≤ L) : 10 ≤ horizon L := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  apply le_of_pow_le_pow_left₀ (by decide : (3:ℕ) ≠ 0) (show 0 ≤ horizon L by unfold horizon; positivity)
  rw [horizon_cube hL0]
  norm_num
  linarith only [hL]

lemma horizon_budget {X : ℝ} {n : ℕ} (hX : 0 < X)
    (hL : 1000000000000 ≤ Real.log X) (hvolume : X ≤ (n:ℝ)^301) :
    horizonBudget (horizon (Real.log X)) ≤ (n:ℝ) := by
  have hL0 : 0 ≤ Real.log X := by linarith only [hL]
  have hτ := horizon_ten hL
  have hτ3 := horizon_cube hL0
  have hp := pow_le_pow_left₀ (by linarith only [hτ] : (0:ℝ) ≤ 1+horizon (Real.log X))
    (by linarith only [hτ] : 1+horizon (Real.log X) ≤ (11/10:ℝ)*horizon (Real.log X)) 3
  rw [mul_pow,hτ3] at hp
  have he : horizonBudget (horizon (Real.log X)) ≤ Real.exp (Real.log X/301) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hp,hL0]
  have hexp : Real.exp (Real.log X/301) = X^(1/301:ℝ) := by
    rw [Real.rpow_def_of_pos hX]
    congr 1
    ring
  rw [hexp] at he
  apply he.trans
  have hr := (Real.rpow_inv_le_iff_of_pos hX.le (Nat.cast_nonneg n) (by norm_num : (0:ℝ) < 301)).mpr
    (show X ≤ (n:ℝ)^(301:ℝ) by
      change X ≤ (n:ℝ)^((301:ℕ):ℝ)
      rw [Real.rpow_natCast]
      exact hvolume)
  norm_num only [inv_eq_one_div] at hr
  exact hr

lemma scale_lower {X L a M : ℝ} {n : ℕ} (hX : 0 < X) (hL : 0 < L)
    (hn : 0 < n) (ha : (3/4:ℝ)*X/L ≤ a)
    (hdegree : (n:ℝ)^300*L^2 ≤ (8/5:ℝ)*X)
    (hM : horizon L*a/(2*(n:ℝ)^100) ≤ M) :
    (1/500:ℝ)*X^(2/3:ℝ) ≤ M := by
  let R : ℝ := (X*L)^(1/3:ℝ)
  have hR : 0 < R := Real.rpow_pos_of_pos (mul_pos hX hL) _
  have hR3 : R^3 = X*L := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast (mul_nonneg hX.le hL.le)]
    norm_num
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hτ : 0 ≤ horizon L := by unfold horizon; positivity
  have hcube : ((n:ℝ)^100*L)^3 ≤ (8/5:ℝ)*X*L := by
    have hh := mul_le_mul_of_nonneg_right hdegree hL.le
    nlinarith only [hh]
  have hden : (8/3:ℝ)*(n:ℝ)^100*L ≤ (25/8:ℝ)*R := by
    have hh : (n:ℝ)^100*L ≤ (75/64:ℝ)*R := by
      apply le_of_pow_le_pow_left₀ (by decide : (3:ℕ) ≠ 0) (by positivity : 0 ≤ (75/64:ℝ)*R)
      rw [show ((75/64:ℝ)*R)^3 = (75/64:ℝ)^3*(X*L) by rw [mul_pow,hR3]]
      nlinarith only [hcube,mul_nonneg hX.le hL.le]
    linarith only [hh]
  have hsmall := div_le_div_of_nonneg_left (show 0 ≤ horizon L*X by positivity)
    (by positivity : 0 < (8/3:ℝ)*(n:ℝ)^100*L) hden
  have hsize := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ha hτ)
    (by positivity : 0 ≤ 2*(n:ℝ)^100)
  have he : horizon L*((3/4:ℝ)*X/L)/(2*(n:ℝ)^100) =
      horizon L*X/((8/3:ℝ)*(n:ℝ)^100*L) := by ring
  rw [he] at hsize
  have hid : horizon L*X/((25/8:ℝ)*R) = (1/500:ℝ)*X^(2/3:ℝ) := by
    have hx : 0 < X^(1/3:ℝ) := Real.rpow_pos_of_pos hX _
    have hl : 0 < L^(1/3:ℝ) := Real.rpow_pos_of_pos hL _
    have hxsum : X^(1/3:ℝ)*X^(2/3:ℝ) = X := by
      rw [← Real.rpow_add hX]
      norm_num
    dsimp [horizon,R]
    rw [Real.mul_rpow hX.le hL.le]
    field_simp
    nlinarith only [hxsum]
  rw [← hid]
  exact hsmall.trans (hsize.trans hM)

#print axioms root_lower
#print axioms volume301
#print axioms root_upper
#print axioms trim_surplus
#print axioms horizon_budget
#print axioms scale_lower
end
end Erdos773.GreedyCodegreeSquareScales
