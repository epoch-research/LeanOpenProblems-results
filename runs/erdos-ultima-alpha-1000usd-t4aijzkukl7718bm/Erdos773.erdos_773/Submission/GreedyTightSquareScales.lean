import Submission.GreedyGrowingSquareScales

/-! Tighter eventual rounding and logarithmic horizons for the square transfer. -/
namespace Erdos773.GreedyTightSquareScales
open Finset Filter GreedySquareScales GreedyGrowingSquareScales GreedyHorizonFactors
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
noncomputable section

def tightHorizon (L : ℝ) : ℝ := L^(1/3:ℝ)/100

lemma ceil_root24_tight {D : ℝ} (hD : 0 ≤ D) (hlarge : 1000 ≤ D^(1/24:ℝ)) :
    (⌈D^(1/24:ℝ)⌉₊:ℝ)^24 ≤ (26/25:ℝ)*D := by
  have hr : 0 ≤ D^(1/24:ℝ) := Real.rpow_nonneg hD _
  have he : (D^(1/24:ℝ))^24 = D := by
    rw [← Real.rpow_mul_natCast hD]
    norm_num
  have hc := Nat.ceil_lt_add_one hr
  have hhi : (⌈D^(1/24:ℝ)⌉₊:ℝ) ≤ (1001/1000:ℝ)*D^(1/24:ℝ) := by
    linarith only [hc,hlarge]
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg _) hhi 24
  rw [mul_pow,he] at hp
  exact hp.trans (mul_le_mul_of_nonneg_right (by norm_num : (1001/1000:ℝ)^24 ≤ 26/25) hD)

/-- The rounded parameter only needs a volume exponent of 97, rather than 192. -/
lemma volume97 {X L : ℝ} (hX : 1 ≤ X) (hL : 0 < L) (hlog : L^2 ≤ X^(1/388:ℝ)) :
    X ≤ (degreeRoot24 X L:ℝ)^97 := by
  have hX0 : 0 < X := by linarith
  have hz : 0 ≤ X^(24/97:ℝ) := Real.rpow_nonneg hX0.le _
  have hprod : X^(24/97:ℝ)*X^(1/388:ℝ) = rootScale X := by
    rw [← Real.rpow_add hX0]
    norm_num [rootScale]
  have hDs : X^(24/97:ℝ) ≤ degreeScale X L := by
    apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
    have hh := mul_le_mul_of_nonneg_left hlog hz
    rw [hprod] at hh
    have hr := (rootScale_pos hX0).le
    nlinarith only [hh,hr]
  have hD1 : 1 ≤ degreeScale X L :=
    (Real.one_le_rpow hX (by norm_num : (0:ℝ) ≤ 24/97)).trans hDs
  have hm := (ceil_root24_bounds hD1).1
  change degreeScale X L ≤ (degreeRoot24 X L:ℝ)^24 at hm
  have hv := pow_le_pow_left₀ hz (hDs.trans hm) 97
  have hz97 : (X^(24/97:ℝ))^97 = X^24 := by
    rw [← Real.rpow_mul_natCast hX0.le]
    norm_num
  rw [hz97] at hv
  apply le_of_pow_le_pow_left₀ (by decide : (24:ℕ) ≠ 0) (by positivity : 0 ≤ (degreeRoot24 X L:ℝ)^97)
  simpa only [← pow_mul,show (24:ℕ)*97=97*24 by omega] using hv

lemma tight_degree {X L : ℝ} (hX : 0 < X) (hL : 0 < L)
    (hm : 1001 ≤ degreeRoot24 X L) :
    (degreeRoot24 X L:ℝ)^24*L^2 ≤ (3328/25:ℝ)*rootScale X := by
  have hD : 0 ≤ degreeScale X L := by unfold degreeScale rootScale; positivity
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg hD (1/24:ℝ))
  have hm' : (1001:ℝ) ≤ degreeRoot24 X L := by exact_mod_cast hm
  change (1001:ℝ) ≤ ⌈(degreeScale X L)^(1/24:ℝ)⌉₊ at hm'
  have hr : 1000 ≤ (degreeScale X L)^(1/24:ℝ) := by linarith only [hc,hm']
  have hb := ceil_root24_tight hD hr
  change (degreeRoot24 X L:ℝ)^24 ≤ (26/25:ℝ)*degreeScale X L at hb
  have hh := mul_le_mul_of_nonneg_right hb (sq_nonneg L)
  have he : ((26/25:ℝ)*degreeScale X L)*L^2 = (3328/25:ℝ)*rootScale X := by
    unfold degreeScale
    field_simp
    ring
  rwa [he] at hh

lemma tightHorizon_cube {L : ℝ} (hL : 0 ≤ L) : (tightHorizon L)^3 = L/1000000 := by
  unfold tightHorizon
  rw [div_pow,← Real.rpow_mul_natCast hL]
  norm_num

lemma tightHorizon_hundred {L : ℝ} (hL : 1000000000000 ≤ L) : 100 ≤ tightHorizon L := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  apply le_of_pow_le_pow_left₀ (by decide : (3:ℕ) ≠ 0)
    (show 0 ≤ tightHorizon L by unfold tightHorizon; positivity)
  rw [tightHorizon_cube hL0]
  norm_num
  linarith only [hL]

lemma tightHorizon_budget {X : ℝ} {n : ℕ} (hX : 0 < X)
    (hL : 1000000000000 ≤ Real.log X) (hvolume : X ≤ (n:ℝ)^97) :
    horizonBudget (tightHorizon (Real.log X)) ≤ (n:ℝ) := by
  have hL0 : 0 ≤ Real.log X := by linarith only [hL]
  have hτ := tightHorizon_hundred hL
  have hτ3 := tightHorizon_cube hL0
  have hp := pow_le_pow_left₀ (by linarith only [hτ] : (0:ℝ) ≤ 1+tightHorizon (Real.log X))
    (by linarith only [hτ] : 1+tightHorizon (Real.log X) ≤ (101/100:ℝ)*tightHorizon (Real.log X)) 3
  rw [mul_pow,hτ3] at hp
  have he : horizonBudget (tightHorizon (Real.log X)) ≤ Real.exp (Real.log X/97) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hp,hL0]
  have hexp : Real.exp (Real.log X/97) = X^(1/97:ℝ) := by
    rw [Real.rpow_def_of_pos hX]
    congr 1
    ring
  rw [hexp] at he
  apply he.trans
  have hr := (Real.rpow_inv_le_iff_of_pos hX.le (Nat.cast_nonneg n) (by norm_num : (0:ℝ) < 97)).mpr
    (show X ≤ (n:ℝ)^(97:ℝ) by
      change X ≤ (n:ℝ)^((97:ℕ):ℝ)
      rw [Real.rpow_natCast]
      exact hvolume)
  norm_num only [inv_eq_one_div] at hr
  exact hr

lemma tight_scale_lower {X L a M : ℝ} {n : ℕ} (hX : 0 < X) (hL : 0 < L)
    (hn : 0 < n) (ha : X/(2*L) ≤ a)
    (hdegree : (n:ℝ)^24*L^2 ≤ (3328/25:ℝ)*rootScale X)
    (hM : tightHorizon L*probability X*a/(8*(n:ℝ)^8) ≤ M) :
    (1/8192:ℝ)*X^(2/3:ℝ) ≤ M := by
  let R : ℝ := (X*L)^(1/3:ℝ)
  have hR : 0 < R := Real.rpow_pos_of_pos (mul_pos hX hL) _
  have hR3 : R^3 = X*L := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast (mul_nonneg hX.le hL.le)]
    norm_num
  have hr := rootScale_pos hX
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hτ : 0 ≤ tightHorizon L := by unfold tightHorizon; positivity
  have hcube : (rootScale X*L*(n:ℝ)^8)^3 ≤ (3328/25:ℝ)*X*L := by
    calc
      _ = ((n:ℝ)^24*L^2)*((rootScale X)^3*L) := by ring
      _ ≤ ((3328/25:ℝ)*rootScale X)*((rootScale X)^3*L) :=
        mul_le_mul_of_nonneg_right hdegree (by positivity)
      _ = (3328/25:ℝ)*(rootScale X)^4*L := by ring
      _ = _ := by rw [rootScale_four hX.le]
  have hden : 16*rootScale X*L*(n:ℝ)^8 ≤ (2048/25:ℝ)*R := by
    have hh : rootScale X*L*(n:ℝ)^8 ≤ (128/25:ℝ)*R := by
      apply le_of_pow_le_pow_left₀ (by decide : (3:ℕ) ≠ 0) (by positivity : 0 ≤ (128/25:ℝ)*R)
      rw [show ((128/25:ℝ)*R)^3 = (128/25:ℝ)^3*(X*L) by rw [mul_pow,hR3]]
      have hprod := mul_nonneg hX.le hL.le
      nlinarith only [hcube,hprod]
    linarith only [hh]
  have hsmall := div_le_div_of_nonneg_left (show 0 ≤ tightHorizon L*X by positivity)
    (by positivity : 0 < 16*rootScale X*L*(n:ℝ)^8) hden
  have hsize := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left ha (show 0 ≤ tightHorizon L*probability X by unfold probability; positivity))
    (by positivity : 0 ≤ 8*(n:ℝ)^8)
  have he : tightHorizon L*probability X*(X/(2*L))/(8*(n:ℝ)^8) =
      tightHorizon L*X/(16*rootScale X*L*(n:ℝ)^8) := by dsimp [probability]; ring
  rw [he] at hsize
  have hfinal := hsmall.trans (hsize.trans hM)
  have hid : tightHorizon L*X/((2048/25:ℝ)*R) = (1/8192:ℝ)*X^(2/3:ℝ) := by
    have hx : 0 < X^(1/3:ℝ) := Real.rpow_pos_of_pos hX _
    have hl : 0 < L^(1/3:ℝ) := Real.rpow_pos_of_pos hL _
    have hxsum : X^(1/3:ℝ)*X^(2/3:ℝ) = X := by
      rw [← Real.rpow_add hX]
      norm_num
    dsimp [tightHorizon,R]
    rw [Real.mul_rpow hX.le hL.le]
    field_simp
    nlinarith only [hxsum]
  rwa [hid] at hfinal

#print axioms ceil_root24_tight
#print axioms volume97
#print axioms tight_degree
#print axioms tightHorizon_cube
#print axioms tightHorizon_hundred
#print axioms tightHorizon_budget
#print axioms tight_scale_lower
end
end Erdos773.GreedyTightSquareScales
