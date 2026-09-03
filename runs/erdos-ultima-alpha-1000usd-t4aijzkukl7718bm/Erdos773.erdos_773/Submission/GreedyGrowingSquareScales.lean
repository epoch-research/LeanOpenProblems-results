import Submission.GreedyGrowingSquareCertificate
import Submission.GreedySquareScales

/-!
Twenty-fourth-root rounding and explicit logarithmic horizons for the square
transfer. All constants and real-power identities are checked exactly.
-/
namespace Erdos773.GreedyGrowingSquareScales
open Finset Filter GreedySquareScales GreedyHorizonFactors
set_option maxHeartbeats 2500000
noncomputable section

def degreeRoot24 (X L : ℝ) : ℕ := ⌈(degreeScale X L)^(1/24:ℝ)⌉₊
def horizon (L : ℝ) : ℝ := (L/15360000)^(1/3:ℝ)
def lowerConstant : ℝ := 1/(32768*(15360000:ℝ)^(1/3:ℝ))

lemma ceil_root24_bounds {D : ℝ} (hD : 1 ≤ D) :
    D ≤ (⌈D^(1/24:ℝ)⌉₊:ℝ)^24 ∧ (⌈D^(1/24:ℝ)⌉₊:ℝ)^24 ≤ 16777216*D := by
  have hD0 : 0 ≤ D := by linarith
  have hr : 0 ≤ D^(1/24:ℝ) := Real.rpow_nonneg hD0 _
  have hr1 : 1 ≤ D^(1/24:ℝ) := Real.one_le_rpow hD (by norm_num)
  have he : (D^(1/24:ℝ))^24 = D := by
    rw [← Real.rpow_mul_natCast hD0]
    norm_num
  have hlo := pow_le_pow_left₀ hr (Nat.le_ceil _) 24
  rw [he] at hlo
  have hceil := Nat.ceil_lt_add_one hr
  have hhi : (⌈D^(1/24:ℝ)⌉₊:ℝ) ≤ 2*D^(1/24:ℝ) := by linarith only [hceil,hr1]
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg _) hhi 24
  rw [mul_pow,he] at hpow
  norm_num at hpow
  exact ⟨hlo,hpow⟩

lemma scalar24_bounds {X L : ℝ} (hX : 1 ≤ X) (hL : 0 < L)
    (hlog : L^2 ≤ X^(1/8:ℝ)) (hlarge : 4 ≤ X^(1/8:ℝ)) :
    0 ≤ probability X ∧ probability X ≤ 1 ∧ 0 < penaltyWeight X L ∧
    8/penaltyWeight X L ≤ (degreeRoot24 X L:ℝ)^24 ∧
    X ≤ (degreeRoot24 X L:ℝ)^192 ∧
    (degreeRoot24 X L:ℝ)^24*L^2 ≤ 2147483648*rootScale X ∧
    (X^(1/16:ℝ))^2 ≤ rootScale X/4 := by
  have hX0 : 0 < X := by linarith
  have hr := rootScale_pos hX0
  have hr1 : 1 ≤ rootScale X := Real.one_le_rpow hX (by norm_num)
  have hLp := sq_pos_of_pos hL
  obtain ⟨hs2,hs8,hK2⟩ := eighth_identities hX0.le
  have hs0 : 0 ≤ X^(1/8:ℝ) := Real.rpow_nonneg hX0.le _
  have hDs : X^(1/8:ℝ) ≤ degreeScale X L := by
    apply (le_div_iff₀ hLp).mpr
    have hh := mul_le_mul_of_nonneg_right hlog hs0
    rw [← pow_two,hs2] at hh
    have hr0 := hr.le
    nlinarith only [hh,hr0]
  have hD1 : 1 ≤ degreeScale X L := (by linarith only [hlarge] : 1 ≤ X^(1/8:ℝ)).trans hDs
  obtain ⟨hmlo,hmhi⟩ := ceil_root24_bounds hD1
  change degreeScale X L ≤ (degreeRoot24 X L:ℝ)^24 at hmlo
  change (degreeRoot24 X L:ℝ)^24 ≤ 16777216*degreeScale X L at hmhi
  have hvol := pow_le_pow_left₀ hs0 (hDs.trans hmlo) 8
  rw [hs8,← pow_mul] at hvol
  have hupper : (degreeRoot24 X L:ℝ)^24*L^2 ≤ 2147483648*rootScale X := by
    have hh := mul_le_mul_of_nonneg_right hmhi hLp.le
    dsimp [degreeScale] at hh
    have he : (16777216*(128*rootScale X/L^2))*L^2 = 2147483648*rootScale X := by field_simp; ring
    rwa [he] at hh
  have hdeg : 8/penaltyWeight X L = degreeScale X L := by
    dsimp [penaltyWeight,degreeScale]
    field_simp
    ring
  refine ⟨by unfold probability; positivity,?_,?_,hdeg ▸ hmlo,hvol,hupper,?_⟩
  · exact (div_le_one hr).mpr hr1
  · unfold penaltyWeight
    positivity
  · rw [hK2,← hs2]
    nlinarith only [mul_le_mul_of_nonneg_right hlarge hs0]

lemma scale_lower {X L a M τ : ℝ} {n : ℕ} (hX : 0 < X) (hL : 0 < L)
    (hn : 0 < n) (hτ : 0 ≤ τ) (ha : X/(2*L) ≤ a)
    (hdegree : (n:ℝ)^24*L^2 ≤ 2147483648*rootScale X)
    (hM : τ*probability X*a/(8*(n:ℝ)^8) ≤ M) :
    τ*X/(32768*(X*L)^(1/3:ℝ)) ≤ M := by
  let R : ℝ := (X*L)^(1/3:ℝ)
  have hR : 0 < R := Real.rpow_pos_of_pos (mul_pos hX hL) _
  have hR3 : R^3 = X*L := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast (mul_nonneg hX.le hL.le)]
    norm_num
  have hr := rootScale_pos hX
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hcube : (rootScale X*L*(n:ℝ)^8)^3 ≤ 2147483648*X*L := by
    calc
      _ = ((n:ℝ)^24*L^2)*((rootScale X)^3*L) := by ring
      _ ≤ (2147483648*rootScale X)*((rootScale X)^3*L) :=
        mul_le_mul_of_nonneg_right hdegree (by positivity)
      _ = 2147483648*(rootScale X)^4*L := by ring
      _ = _ := by rw [rootScale_four hX.le]
  have hden : 16*rootScale X*L*(n:ℝ)^8 ≤ 32768*R := by
    have hh : rootScale X*L*(n:ℝ)^8 ≤ 2048*R := by
      apply le_of_pow_le_pow_left₀ (by omega : (3:ℕ) ≠ 0) (by positivity : 0 ≤ 2048*R)
      rw [show (2048*R)^3 = 2048^3*(X*L) by rw [mul_pow,hR3]]
      have hn := mul_nonneg hX.le hL.le
      nlinarith only [hcube,hn]
    nlinarith only [hh]
  have hsmall := div_le_div_of_nonneg_left (show 0 ≤ τ*X by positivity)
    (by positivity : 0 < 16*rootScale X*L*(n:ℝ)^8) hden
  have hsize := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left ha (show 0 ≤ τ*probability X by unfold probability; positivity))
    (by positivity : 0 ≤ 8*(n:ℝ)^8)
  have he : τ*probability X*(X/(2*L))/(8*(n:ℝ)^8) =
      τ*X/(16*rootScale X*L*(n:ℝ)^8) := by dsimp [probability]; ring
  rw [he] at hsize
  exact hsmall.trans (hsize.trans hM)

lemma horizon_cube {L : ℝ} (hL : 0 ≤ L) : (horizon L)^3 = L/15360000 := by
  dsimp [horizon]
  rw [← Real.rpow_mul_natCast (by positivity : (0:ℝ) ≤ L/15360000)]
  norm_num

lemma horizon_one {L : ℝ} (hL : 15360000 ≤ L) : 1 ≤ horizon L := by
  apply Real.one_le_rpow _ (by norm_num : (0:ℝ) ≤ 1/3)
  linarith only [hL]

lemma horizon_budget {X : ℝ} {n : ℕ} (hX : 0 < X) (hL : 15360000 ≤ Real.log X)
    (hvolume : X ≤ (n:ℝ)^192) : horizonBudget (horizon (Real.log X)) ≤ (n:ℝ) := by
  have hL0 : 0 ≤ Real.log X := by linarith only [hL]
  have hτ := horizon_one hL
  have hτ3 := horizon_cube hL0
  have hpow := pow_le_pow_left₀ (by linarith only [hτ] : (0:ℝ) ≤ 1+horizon (Real.log X))
    (by linarith only [hτ] : 1+horizon (Real.log X) ≤ 2*horizon (Real.log X)) 3
  have hexp : horizonBudget (horizon (Real.log X)) ≤ Real.exp (Real.log X/192) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hpow,hτ3]
  have he : Real.exp (Real.log X/192) = X^(1/192:ℝ) := by
    rw [Real.rpow_def_of_pos hX]
    congr 1
    ring
  rw [he] at hexp
  apply hexp.trans
  have hroot := (Real.rpow_inv_le_iff_of_pos hX.le (Nat.cast_nonneg n) (by norm_num : (0:ℝ) < 192)).mpr
    (show X ≤ (n:ℝ)^(192:ℝ) by
      change X ≤ (n:ℝ)^((192:ℕ):ℝ)
      rw [Real.rpow_natCast]
      exact hvolume)
  norm_num only [inv_eq_one_div] at hroot
  exact hroot

lemma lowerConstant_pos : 0 < lowerConstant := by unfold lowerConstant; positivity

lemma lower_identity {X L : ℝ} (hX : 0 < X) (hL : 0 < L) :
    horizon L*X/(32768*(X*L)^(1/3:ℝ)) = lowerConstant*X^(2/3:ℝ) := by
  have hx := Real.rpow_pos_of_pos hX (1/3:ℝ)
  have hl := Real.rpow_pos_of_pos hL (1/3:ℝ)
  have hc : 0 < (15360000:ℝ)^(1/3:ℝ) := by positivity
  have hxsum : X^(1/3:ℝ)*X^(2/3:ℝ) = X := by
    rw [← Real.rpow_add hX]
    norm_num
  unfold horizon lowerConstant
  rw [Real.div_rpow hL.le (by norm_num : (0:ℝ) ≤ 15360000),Real.mul_rpow hX.le hL.le]
  field_simp
  nlinarith only [hxsum]

#print axioms scalar24_bounds
#print axioms scale_lower
#print axioms horizon_budget
#print axioms lower_identity
end
end Erdos773.GreedyGrowingSquareScales
