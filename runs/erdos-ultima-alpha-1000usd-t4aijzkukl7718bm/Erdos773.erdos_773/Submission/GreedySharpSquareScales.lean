import Submission.GreedyTightSquareScales

/-! Using the proved collision coefficient, without any new probabilistic
hypothesis, improves the actual lower bound to N^(2/3)/1200. -/
namespace Erdos773.GreedySharpSquareScales
open Finset Filter GreedySquareScales GreedyGrowingSquareScales GreedyTightSquareScales
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
noncomputable section

def sharpWeight (X L : ℝ) : ℝ := 3*L^2/rootScale X
def sharpDegree (X L : ℝ) : ℝ := (8/3:ℝ)*rootScale X/L^2
def sharpRoot24 (X L : ℝ) : ℕ := ⌈(sharpDegree X L)^(1/24:ℝ)⌉₊

lemma scalar_bounds {X L : ℝ} (hX : 1 ≤ X) (hL : 0 < L)
    (hlog : L^2 ≤ X^(1/8:ℝ)) (hlarge : 4 ≤ X^(1/8:ℝ)) :
    0 ≤ probability X ∧ probability X ≤ 1 ∧ 0 < sharpWeight X L ∧
    8/sharpWeight X L ≤ (sharpRoot24 X L:ℝ)^24 ∧
    (X^(1/16:ℝ))^2 ≤ rootScale X/4 := by
  have hX0 : 0 < X := by linarith
  have hr := rootScale_pos hX0
  have hr1 : 1 ≤ rootScale X := Real.one_le_rpow hX (by norm_num)
  have hLp := sq_pos_of_pos hL
  obtain ⟨hs2,_,hK2⟩ := eighth_identities hX0.le
  have hs0 : 0 ≤ X^(1/8:ℝ) := Real.rpow_nonneg hX0.le _
  have hDs : X^(1/8:ℝ) ≤ sharpDegree X L := by
    apply (le_div_iff₀ hLp).mpr
    have hh := mul_le_mul_of_nonneg_right hlog hs0
    rw [← pow_two,hs2] at hh
    have hr0 := hr.le
    nlinarith only [hh,hr0]
  have hD1 : 1 ≤ sharpDegree X L :=
    (by linarith only [hlarge] : 1 ≤ X^(1/8:ℝ)).trans hDs
  have hmlo := (ceil_root24_bounds hD1).1
  change sharpDegree X L ≤ (sharpRoot24 X L:ℝ)^24 at hmlo
  have hdeg : 8/sharpWeight X L = sharpDegree X L := by
    dsimp [sharpWeight,sharpDegree]
    field_simp
  refine ⟨by unfold probability; positivity,?_,?_,hdeg ▸ hmlo,?_⟩
  · exact (div_le_one hr).mpr hr1
  · unfold sharpWeight
    positivity
  · rw [hK2,← hs2]
    nlinarith only [mul_le_mul_of_nonneg_right hlarge hs0]

lemma retained_edge_cost {X L a E : ℝ} (hX : 0 < X) (hL : 0 < L)
    (ha : (999/1000:ℝ)*X/L ≤ a) (hE : E ≤ (83/1000:ℝ)*X^2/L^3) :
    sharpWeight X L*(probability X)^4*E ≤ probability X*a/4 := by
  have hr := rootScale_pos hX
  have hp : 0 ≤ probability X := by unfold probability; positivity
  have hμ : 0 ≤ sharpWeight X L := by unfold sharpWeight; positivity
  have hh := mul_le_mul_of_nonneg_left hE (mul_nonneg hμ (pow_nonneg hp 4))
  have he : sharpWeight X L*(probability X)^4*((83/1000:ℝ)*X^2/L^3) =
      (249/1000:ℝ)*probability X*X/L := by
    dsimp [sharpWeight,probability]
    have hroot := rootScale_four hX.le
    generalize rootScale X = r at hr hroot ⊢
    rw [← hroot]
    field_simp
    ring
  rw [he] at hh
  have hsize := mul_le_mul_of_nonneg_left ha hp
  have hn : 0 ≤ probability X*X/L := by positivity
  have hid : probability X*((999/1000:ℝ)*X/L) =
      (999/1000:ℝ)*(probability X*X/L) := by ring
  rw [hid] at hsize
  have hh' : sharpWeight X L*(probability X)^4*E ≤
      (249/1000:ℝ)*(probability X*X/L) := by
    convert hh using 1; ring
  linarith only [hh',hsize,hn]

/-- The rounded parameter only needs a volume exponent of 97, rather than 192. -/
lemma volume97 {X L : ℝ} (hX : 1 ≤ X) (hL : 0 < L) (hlog : L^2 ≤ X^(1/388:ℝ)) :
    X ≤ (sharpRoot24 X L:ℝ)^97 := by
  have hX0 : 0 < X := by linarith
  have hz : 0 ≤ X^(24/97:ℝ) := Real.rpow_nonneg hX0.le _
  have hprod : X^(24/97:ℝ)*X^(1/388:ℝ) = rootScale X := by
    rw [← Real.rpow_add hX0]
    norm_num [rootScale]
  have hDs : X^(24/97:ℝ) ≤ sharpDegree X L := by
    apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
    have hh := mul_le_mul_of_nonneg_left hlog hz
    rw [hprod] at hh
    have hr := (rootScale_pos hX0).le
    nlinarith only [hh,hr]
  have hD1 : 1 ≤ sharpDegree X L :=
    (Real.one_le_rpow hX (by norm_num : (0:ℝ) ≤ 24/97)).trans hDs
  have hm := (ceil_root24_bounds hD1).1
  change sharpDegree X L ≤ (sharpRoot24 X L:ℝ)^24 at hm
  have hv := pow_le_pow_left₀ hz (hDs.trans hm) 97
  have hz97 : (X^(24/97:ℝ))^97 = X^24 := by
    rw [← Real.rpow_mul_natCast hX0.le]
    norm_num
  rw [hz97] at hv
  apply le_of_pow_le_pow_left₀ (by decide : (24:ℕ) ≠ 0) (by positivity : 0 ≤ (sharpRoot24 X L:ℝ)^97)
  simpa only [← pow_mul,show (24:ℕ)*97=97*24 by omega] using hv

lemma sharp_degree {X L : ℝ} (hX : 0 < X) (hL : 0 < L)
    (hm : 1001 ≤ sharpRoot24 X L) :
    (sharpRoot24 X L:ℝ)^24*L^2 ≤ (208/75:ℝ)*rootScale X := by
  have hD : 0 ≤ sharpDegree X L := by unfold sharpDegree rootScale; positivity
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg hD (1/24:ℝ))
  have hm' : (1001:ℝ) ≤ sharpRoot24 X L := by exact_mod_cast hm
  change (1001:ℝ) ≤ ⌈(sharpDegree X L)^(1/24:ℝ)⌉₊ at hm'
  have hr : 1000 ≤ (sharpDegree X L)^(1/24:ℝ) := by linarith only [hc,hm']
  have hb := ceil_root24_tight hD hr
  change (sharpRoot24 X L:ℝ)^24 ≤ (26/25:ℝ)*sharpDegree X L at hb
  have hh := mul_le_mul_of_nonneg_right hb (sq_nonneg L)
  have he : ((26/25:ℝ)*sharpDegree X L)*L^2 = (208/75:ℝ)*rootScale X := by
    unfold sharpDegree
    field_simp
    ring
  rwa [he] at hh

lemma sharp_scale_lower {X L a M : ℝ} {n : ℕ} (hX : 0 < X) (hL : 0 < L)
    (hn : 0 < n) (ha : (20/21:ℝ)*X/L ≤ a)
    (hdegree : (n:ℝ)^24*L^2 ≤ (208/75:ℝ)*rootScale X)
    (hM : tightHorizon L*probability X*a/(8*(n:ℝ)^8) ≤ M) :
    (1/1200:ℝ)*X^(2/3:ℝ) ≤ M := by
  let R : ℝ := (X*L)^(1/3:ℝ)
  have hR : 0 < R := Real.rpow_pos_of_pos (mul_pos hX hL) _
  have hR3 : R^3 = X*L := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast (mul_nonneg hX.le hL.le)]
    norm_num
  have hr := rootScale_pos hX
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hτ : 0 ≤ tightHorizon L := by unfold tightHorizon; positivity
  have hcube : (rootScale X*L*(n:ℝ)^8)^3 ≤ (208/75:ℝ)*X*L := by
    calc
      _ = ((n:ℝ)^24*L^2)*((rootScale X)^3*L) := by ring
      _ ≤ ((208/75:ℝ)*rootScale X)*((rootScale X)^3*L) :=
        mul_le_mul_of_nonneg_right hdegree (by positivity)
      _ = (208/75:ℝ)*(rootScale X)^4*L := by ring
      _ = _ := by rw [rootScale_four hX.le]
  have hden : (42/5:ℝ)*rootScale X*L*(n:ℝ)^8 ≤ (12:ℝ)*R := by
    have hh : rootScale X*L*(n:ℝ)^8 ≤ (10/7:ℝ)*R := by
      apply le_of_pow_le_pow_left₀ (by decide : (3:ℕ) ≠ 0) (by positivity : 0 ≤ (10/7:ℝ)*R)
      rw [show ((10/7:ℝ)*R)^3 = (10/7:ℝ)^3*(X*L) by rw [mul_pow,hR3]]
      have hprod := mul_nonneg hX.le hL.le
      nlinarith only [hcube,hprod]
    linarith only [hh]
  have hsmall := div_le_div_of_nonneg_left (show 0 ≤ tightHorizon L*X by positivity)
    (by positivity : 0 < (42/5:ℝ)*rootScale X*L*(n:ℝ)^8) hden
  have hsize := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left ha (show 0 ≤ tightHorizon L*probability X by unfold probability; positivity))
    (by positivity : 0 ≤ 8*(n:ℝ)^8)
  have he : tightHorizon L*probability X*((20/21:ℝ)*X/L)/(8*(n:ℝ)^8) =
      tightHorizon L*X/((42/5:ℝ)*rootScale X*L*(n:ℝ)^8) := by dsimp [probability]; ring
  rw [he] at hsize
  have hfinal := hsmall.trans (hsize.trans hM)
  have hid : tightHorizon L*X/((12:ℝ)*R) = (1/1200:ℝ)*X^(2/3:ℝ) := by
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

#print axioms scalar_bounds
#print axioms retained_edge_cost
#print axioms volume97
#print axioms sharp_degree
#print axioms sharp_scale_lower
end
end Erdos773.GreedySharpSquareScales
