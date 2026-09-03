import Submission.GreedySquareCertificate

/-!
Rounding and algebra for the square-specific thinning scale. These finite
estimates retain the logarithmic factors rather than absorbing them into
an arbitrary power loss.
-/
namespace Erdos773.GreedySquareScales
open Finset Filter
set_option maxHeartbeats 2500000
noncomputable section

def rootScale (X : ℝ) : ℝ := X^(1/4:ℝ)
def probability (X : ℝ) : ℝ := 1/rootScale X
def penaltyWeight (X L : ℝ) : ℝ := L^2/(16*rootScale X)
def degreeScale (X L : ℝ) : ℝ := 128*rootScale X/L^2
def degreeRoot (X L : ℝ) : ℕ := ⌈(degreeScale X L)^(1/12:ℝ)⌉₊

lemma rootScale_pos {X : ℝ} (hX : 0 < X) : 0 < rootScale X := Real.rpow_pos_of_pos hX _
lemma rootScale_four {X : ℝ} (hX : 0 ≤ X) : (rootScale X)^4 = X := by
  rw [rootScale,← Real.rpow_mul_natCast hX]
  norm_num

lemma ceil_root_bounds {D : ℝ} (hD : 1 ≤ D) :
    D ≤ (⌈D^(1/12:ℝ)⌉₊:ℝ)^12 ∧ (⌈D^(1/12:ℝ)⌉₊:ℝ)^12 ≤ 4096*D := by
  have hD0 : 0 ≤ D := by linarith
  have hr : 0 ≤ D^(1/12:ℝ) := Real.rpow_nonneg hD0 _
  have hr1 : 1 ≤ D^(1/12:ℝ) := Real.one_le_rpow hD (by norm_num)
  have he : (D^(1/12:ℝ))^12 = D := by
    rw [← Real.rpow_mul_natCast hD0]
    norm_num
  have hlo := pow_le_pow_left₀ hr (Nat.le_ceil _) 12
  rw [he] at hlo
  have hceil := Nat.ceil_lt_add_one hr
  have hhi : (⌈D^(1/12:ℝ)⌉₊:ℝ) ≤ 2*D^(1/12:ℝ) := by linarith only [hceil,hr1]
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg _) hhi 12
  rw [mul_pow,he] at hpow
  norm_num at hpow
  exact ⟨hlo,hpow⟩

lemma eighth_identities {X : ℝ} (hX : 0 ≤ X) :
    (X^(1/8:ℝ))^2 = rootScale X ∧ (X^(1/8:ℝ))^8 = X ∧
    (X^(1/16:ℝ))^2 = X^(1/8:ℝ) := by
  dsimp [rootScale]
  constructor
  · rw [← Real.rpow_mul_natCast hX]; norm_num
  constructor
  · rw [← Real.rpow_mul_natCast hX]; norm_num
  · rw [← Real.rpow_mul_natCast hX]; norm_num

lemma scalar_bounds {X L : ℝ} (hX : 1 ≤ X) (hL : 0 < L)
    (hlog : L^2 ≤ X^(1/8:ℝ)) (hlarge : 4 ≤ X^(1/8:ℝ)) :
    0 ≤ probability X ∧ probability X ≤ 1 ∧ 0 < penaltyWeight X L ∧
    8/penaltyWeight X L ≤ (degreeRoot X L:ℝ)^12 ∧
    X ≤ (degreeRoot X L:ℝ)^96 ∧
    (degreeRoot X L:ℝ)^12*L^2 ≤ 524288*rootScale X ∧
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
  obtain ⟨hmlo,hmhi⟩ := ceil_root_bounds hD1
  change degreeScale X L ≤ (degreeRoot X L:ℝ)^12 at hmlo
  change (degreeRoot X L:ℝ)^12 ≤ 4096*degreeScale X L at hmhi
  have hvol := pow_le_pow_left₀ hs0 (hDs.trans hmlo) 8
  rw [hs8,← pow_mul] at hvol
  have hupper : (degreeRoot X L:ℝ)^12*L^2 ≤ 524288*rootScale X := by
    have hh := mul_le_mul_of_nonneg_right hmhi hLp.le
    dsimp [degreeScale] at hh
    have he : (4096*(128*rootScale X/L^2))*L^2 = 524288*rootScale X := by field_simp; ring
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

lemma overlap_cost {X a K : ℝ} (hX : 0 < X) (ha : 0 ≤ a) (haX : a ≤ X)
    (hK : K^2 ≤ rootScale X/4) :
    (probability X)^6*a^2*K^2 ≤ probability X*a/4 := by
  have hr := rootScale_pos hX
  have hp : 0 ≤ probability X := by unfold probability; positivity
  have hnum := mul_le_mul haX hK (sq_nonneg K) hX.le
  have hsmall : (probability X)^5*a*K^2 ≤ 1/4 := by
    have hh := mul_le_mul_of_nonneg_left hnum (pow_nonneg hp 5)
    have he : (probability X)^5*(X*(rootScale X/4)) = 1/4 := by
      dsimp [probability]
      have hroot := rootScale_four hX.le
      generalize rootScale X = r at hr hroot ⊢
      rw [← hroot]
      field_simp
    nlinarith only [hh,he]
  have hm := mul_le_mul_of_nonneg_left hsmall (mul_nonneg hp ha)
  nlinarith only [hm]

lemma retained_edge_cost {X L a E : ℝ} (hX : 0 < X) (hL : 0 < L)
    (ha : X/(2*L) ≤ a) (hE : E ≤ X^2/L^3) :
    penaltyWeight X L*(probability X)^4*E ≤ probability X*a/4 := by
  have hr := rootScale_pos hX
  have hp : 0 ≤ probability X := by unfold probability; positivity
  have hμ : 0 ≤ penaltyWeight X L := by unfold penaltyWeight; positivity
  have hh := mul_le_mul_of_nonneg_left hE (mul_nonneg hμ (pow_nonneg hp 4))
  have he : penaltyWeight X L*(probability X)^4*(X^2/L^3) = probability X*(X/(2*L))/8 := by
    dsimp [penaltyWeight,probability]
    have hroot := rootScale_four hX.le
    generalize rootScale X = r at hr hroot ⊢
    rw [← hroot]
    field_simp
    ring
  rw [he] at hh
  have hsize := mul_le_mul_of_nonneg_left ha hp
  have hn : 0 ≤ probability X*(X/(2*L)) := by positivity
  linarith only [hh,hsize,hn]

/-- Pure algebra converting the finite greedy certificate into the familiar
    N^(2/3)/(log N)^(1/3) scale, with an arbitrary multiplier. -/
lemma scale_lower {X L a M c : ℝ} {m : ℕ} (hX : 0 < X) (hL : 0 < L)
    (hm : 0 < m) (hc : 0 ≤ c) (ha : X/(2*L) ≤ a)
    (hdegree : (m:ℝ)^12*L^2 ≤ 524288*rootScale X)
    (hM : (1024*c)*probability X*a/(4*(m:ℝ)^4) ≤ M) :
    c*X/(X*L)^(1/3:ℝ) ≤ M := by
  let R : ℝ := (X*L)^(1/3:ℝ)
  have hR : 0 < R := Real.rpow_pos_of_pos (mul_pos hX hL) _
  have hR3 : R^3 = X*L := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast (mul_nonneg hX.le hL.le)]
    norm_num
  have hr := rootScale_pos hX
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hcube : (rootScale X*L*(m:ℝ)^4)^3 ≤ 524288*X*L := by
    calc
      _ = ((m:ℝ)^12*L^2)*((rootScale X)^3*L) := by ring
      _ ≤ (524288*rootScale X)*((rootScale X)^3*L) :=
        mul_le_mul_of_nonneg_right hdegree (by positivity)
      _ = _ := by
        calc
          _ = 524288*(rootScale X)^4*L := by ring
          _ = _ := by rw [rootScale_four hX.le]
  have hden : rootScale X*L*(m:ℝ)^4 ≤ 128*R := by
    apply le_of_pow_le_pow_left₀ (by omega : (3:ℕ) ≠ 0) (by positivity : 0 ≤ 128*R)
    rw [show (128*R)^3 = 128^3*(X*L) by rw [mul_pow,hR3]]
    have hn := mul_nonneg hX.le hL.le
    nlinarith only [hcube,hn]
  have hsmall := div_le_div_of_nonneg_left (show 0 ≤ 128*c*X by positivity)
    (by positivity : 0 < rootScale X*L*(m:ℝ)^4) hden
  have hsize := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left ha (show 0 ≤ (1024*c)*probability X by unfold probability; positivity))
    (by positivity : 0 ≤ 4*(m:ℝ)^4)
  have he1 : 128*c*X/(128*R) = c*X/R := by ring
  have he2 : (1024*c)*probability X*(X/(2*L))/(4*(m:ℝ)^4) =
      128*c*X/(rootScale X*L*(m:ℝ)^4) := by dsimp [probability]; ring
  rw [he1] at hsmall
  rw [he2] at hsize
  exact hsmall.trans (hsize.trans hM)

#print axioms scalar_bounds
#print axioms overlap_cost
#print axioms retained_edge_cost
#print axioms scale_lower
end
end Erdos773.GreedySquareScales
