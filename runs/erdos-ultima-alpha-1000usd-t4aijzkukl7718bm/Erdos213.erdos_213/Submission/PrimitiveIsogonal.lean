import Mathlib.Tactic

/-! The most direct isogonal extension of the primitive four-point family
fails at every integer parameter m>=4. This is not a theorem about arbitrary
extensions or arbitrary point configurations. -/
namespace Erdos213.PrimitiveIsogonal

def numerator {R : Type*} [CommRing R] (m : R) : R :=
  2304*m^8-1760*m^6+713*m^4-110*m^2+9
def approx {R : Type*} [CommRing R] (m : R) : R := 1296*m^4-495*m^2+106

def denom {R : Type*} [CommRing R] (m : R) : R := 16*m^4-m^2+1

def rx (m : ℚ) : ℚ := 2*(m^2-1)*(16*m^2-1)/denom m
def ry (m : ℚ) : ℚ := 10*m*(4*m^2-1)/denom m

lemma lower_gap {R : Type*} [CommRing R] (m : R) :
    729*numerator m-(approx m)^2=275*(90*m^2-17) := by
  unfold numerator approx
  ring
lemma upper_gap {R : Type*} [CommRing R] (m : R) :
    (approx m+1)^2-729*numerator m=4*(648*m^4-6435*m^2+1222) := by
  unfold numerator approx
  ring

lemma not_square_between {n a : ℤ} (ha : 0≤a) (hl : a^2<n) (hu : n<(a+1)^2) :
    ¬ IsSquare n := by
  rintro ⟨r,hr⟩
  have hl' : a < |r| := by nlinarith only [hl,hr,sq_abs r,abs_nonneg r,ha]
  have hu' : |r| < a+1 := by nlinarith only [hu,hr,sq_abs r,abs_nonneg r,ha]
  omega

lemma numerator_not_square {m : ℤ} (hm : 4≤m) :
    ¬ IsSquare ((numerator m : ℤ) : ℚ) := by
  have hm2 : (16 : ℤ)≤m^2 := by nlinarith only [hm]
  have hm4 : (16 : ℤ)*m^2≤m^4 := by
    nlinarith only [mul_nonneg (sq_nonneg m) (sub_nonneg.mpr hm2)]
  have ha : 0≤approx m := by unfold approx; nlinarith only [hm2,hm4]
  have hl : (approx m)^2<729*numerator m := by
    nlinarith only [lower_gap m,hm2]
  have hu : 729*numerator m<(approx m+1)^2 := by
    nlinarith only [upper_gap m,hm2,hm4]
  intro hs
  have hs' : IsSquare (numerator m : ℤ) := Rat.isSquare_intCast_iff.mp hs
  exact not_square_between ha hl hu
    ((show IsSquare (729 : ℤ) from ⟨27,by norm_num⟩).mul hs')

lemma denom_ne_zero {m : ℤ} (hm : 4≤m) : denom (m : ℚ) ≠ 0 := by
  have hmQ : (4 : ℚ)≤m := by exact_mod_cast hm
  have hm2 : (16 : ℚ)≤(m : ℚ)^2 := by nlinarith only [hmQ]
  have hm4 : (16 : ℚ)*(m : ℚ)^2≤(m : ℚ)^4 := by
    nlinarith only [mul_nonneg (sq_nonneg (m : ℚ)) (sub_nonneg.mpr hm2)]
  unfold denom
  nlinarith only [hm2,hm4]

lemma missing_square_identity (m : ℚ) (hd : denom m ≠ 0) :
    (rx m+1)^2+(ry m)^2=numerator m/(denom m)^2 := by
  unfold rx ry numerator
  field_simp
  unfold denom
  ring

lemma anchor_square_identities (m : ℚ) (hm : m ≠ 0) (hd : denom m ≠ 0) :
    ((rx m-1)^2+(ry m)^2=((m^2+1)*(16*m^2+1)/denom m)^2) ∧
    ((rx m)^2+(ry m-(m^2-1)/(2*m))^2=
      ((16*m^2-1)*(m^2+1)^2/(2*m*denom m))^2) ∧
    ((rx m)^2+(ry m-(16*m^2-1)/(8*m))^2=
      ((m^2-1)*(16*m^2+1)^2/(8*m*denom m))^2) := by
  unfold rx ry
  constructor
  · field_simp
    unfold denom
    ring
  constructor
  · field_simp
    unfold denom
    ring
  · field_simp
    unfold denom
    ring

/-- The new point is compatible with three anchors, but never with the fourth
at an integer parameter m>=4. -/
theorem fourth_anchor_not_square {m : ℤ} (hm : 4≤m) :
    ¬ IsSquare ((rx (m : ℚ)+1)^2+(ry (m : ℚ))^2) := by
  rw [missing_square_identity _ (denom_ne_zero hm)]
  intro h
  have hh := h.mul (IsSquare.sq (denom (m : ℚ)))
  have he : (denom (m : ℚ))^2 ≠ 0 := pow_ne_zero _ (denom_ne_zero hm)
  rw [div_mul_cancel₀ _ he] at hh
  apply numerator_not_square hm
  simpa only [numerator,Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_ofNat] using hh

#print axioms numerator_not_square
#print axioms anchor_square_identities
#print axioms fourth_anchor_not_square
end Erdos213.PrimitiveIsogonal
