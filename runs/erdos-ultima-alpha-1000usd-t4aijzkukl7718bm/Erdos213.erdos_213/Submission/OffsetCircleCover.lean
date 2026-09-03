import Submission.OffsetCircle

/-! Branch-separation certificates for one extra off-axis point in the
squared offset-circle family. This does not give a general cardinality bound. -/
namespace Erdos213.OffsetCircle

def anchorA (c s : ℚ) : ℚ := (c+1)^2+c^2*s^2
def anchorB (c s : ℚ) : ℚ := c^2+(c-1)^2*s^2

def resAB (c : ℚ) : ℚ := (c^4-(c+1)^2*(c-1)^2)^2
def resAK (c t : ℚ) : ℚ :=
  (c^2*((c+1)^2+c^2*t^2)-(c+1)^2*(c^2+(c-1)^2*t^2))^2+
    c^2*(c+1)^2*(2*t)^2
def resBK (c t : ℚ) : ℚ :=
  ((c-1)^2*((c+1)^2+c^2*t^2)-c^2*(c^2+(c-1)^2*t^2))^2+
    (c-1)^2*c^2*(2*t)^2

lemma resAB_formula (c : ℚ) : resAB c=(2*c^2-1)^2 := by
  dsimp [resAB]
  ring
lemma resAK_formula (c t : ℚ) : resAK c t=
    t^2*((2*c^2-1)^2*t^2+4*c^2*(c+1)^2) := by
  dsimp [resAK]
  ring
lemma resBK_formula (c t : ℚ) : resBK c t=
    (2*c^2-1)^2+4*c^2*(c-1)^2*t^2 := by
  dsimp [resBK]
  ring

lemma twice_square_ne_one (c : ℚ) : 2*c^2 ≠ 1 := by
  have h : ¬ IsSquare (2 : ℚ) := by decide +kernel
  intro he
  apply h
  exact ⟨2*c,by nlinarith only [he]⟩

lemma resAB_pos (c : ℚ) : 0 < resAB c := by
  rw [resAB_formula]
  exact sq_pos_of_ne_zero (sub_ne_zero.mpr (twice_square_ne_one c))
lemma resAK_pos (c t : ℚ) (ht : t ≠ 0) : 0 < resAK c t := by
  rw [resAK_formula]
  have h1 : 0 < (2*c^2-1)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr (twice_square_ne_one c))
  have h2 : 0 < t^2 := sq_pos_of_ne_zero ht
  positivity
lemma resBK_pos (c t : ℚ) : 0 < resBK c t := by
  rw [resBK_formula]
  have h1 : 0 < (2*c^2-1)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr (twice_square_ne_one c))
  positivity

/-- An elementary resultant identity, valid without division. -/
lemma even_quadratic_resultant_identity {R : Type*} [CommRing R] (a e b d f z : R) :
    (a*f-b*e)^2+a*e*d^2 =
      a*d^2*(a*z^2+e)-
        (a*(b*z^2+d*z+f)-b*(a*z^2+e))*(a*d*z-(a*f-b*e)) := by ring

lemma even_quadratic_common_root {R : Type*} [CommRing R] (a e b d f z : R)
    (h1 : a*z^2+e=0) (h2 : b*z^2+d*z+f=0) :
    (a*f-b*e)^2+a*e*d^2=0 := by
  rw [even_quadratic_resultant_identity a e b d f z,h1,h2]
  ring

lemma three_pairwise_resultants_nonzero (c t : ℚ) (ht : t ≠ 0) :
    resAB c ≠ 0 ∧ resAK c t ≠ 0 ∧ resBK c t ≠ 0 :=
  ⟨ne_of_gt (resAB_pos c),ne_of_gt (resAK_pos c t ht),ne_of_gt (resBK_pos c t)⟩

lemma three_discriminants_negative (c t : ℚ) (hc : c ≠ 0) (hp : c ≠ -1)
    (hm : c ≠ 1) (hn : (c+1)+(c-1)*t^2 ≠ 0) :
    -4*c^2*(c+1)^2 < 0 ∧ -4*c^2*(c-1)^2 < 0 ∧
      (2*t)^2-4*(c^2+(c-1)^2*t^2)*((c+1)^2+c^2*t^2) < 0 := by
  have hc2 : 0<c^2 := sq_pos_of_ne_zero hc
  have hp2 : 0<(c+1)^2 := sq_pos_of_ne_zero (by intro h; apply hp; linarith only [h])
  have hm2 : 0<(c-1)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hm)
  have hn2 : 0<((c+1)+(c-1)*t^2)^2 := sq_pos_of_ne_zero hn
  have he : (2*t)^2-4*(c^2+(c-1)^2*t^2)*((c+1)^2+c^2*t^2)=
      -4*c^2*((c+1)+(c-1)*t^2)^2 := by ring
  rw [he]
  constructor
  · exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hc2) hp2
  constructor
  · exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hc2) hm2
  · exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hc2) hn2

lemma zero_kernel_discriminant_real_image (c t : ℚ)
    (hn : (c+1)+(c-1)*t^2=0) : (point c 1 t).2=0 := by
  have hden : 1+t^2 ≠ 0 := by positivity
  have hs : (source c 1 t).1=0 := by
    dsimp [source]
    field_simp
    linear_combination hn
  dsimp [point]
  rw [hs]
  ring

/-- Two endpoint-compatible parameters need not have a rational mutual distance
kernel. In the cubic model the second parameter comes from doubling the seed. -/
lemma doubling_not_distance_preserving :
    IsSquare (anchorA (3/2) 4) ∧ IsSquare (anchorB (3/2) 4) ∧
    IsSquare (anchorA (3/2) (693/520)) ∧ IsSquare (anchorB (3/2) (693/520)) ∧
    ¬ IsSquare (kernel (3/2) 1 4 (693/520)) := by
  decide +kernel

lemma distance_square_iff_kernel (c t s : ℚ) (hts : t ≠ s) :
    IsSquare (distSq 1 (point c 1 t) (point c 1 s)) ↔ IsSquare (kernel c 1 t s) := by
  let f := 4*(t-s)/((1+t^2)*(1+s^2))
  have hdt : 1+t^2 ≠ 0 := by positivity
  have hds : 1+s^2 ≠ 0 := by positivity
  have hf : f ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hts))
    (mul_ne_zero hdt hds)
  have he : distSq 1 (point c 1 t) (point c 1 s)=f^2*kernel c 1 t s := by
    rw [distance_factor c 1 t s (by norm_num)]
    dsimp [f]
    field_simp
    ring
  constructor
  · intro h
    convert h.div (IsSquare.sq f) using 1
    rw [he]
    field_simp
  · intro h
    rw [he]
    exact (IsSquare.sq f).mul h

lemma doubled_seed_distance_not_square :
    ¬ IsSquare (distSq 1 (point (3/2) 1 4) (point (3/2) 1 (693/520))) := by
  rw [distance_square_iff_kernel (3/2) 4 (693/520) (by norm_num)]
  exact doubling_not_distance_preserving.2.2.2.2

/-- The usual tangent formula at the seed has the x-coordinate associated
with 693/520. This certificate is algebraic, not an elliptic-group theorem. -/
lemma doubled_seed_coordinate :
    let m : ℚ := (3*9^2+2*(53/8)*9+2025/256)/(2*(585/16))
    m^2-53/8-2*9=ellipticX (3/2) (693/520) ∧
      -585/16+m*(9-(m^2-53/8-2*9))=35442394911/8998912000 := by
  decide +kernel

#print axioms distance_square_iff_kernel
#print axioms doubled_seed_distance_not_square
#print axioms doubled_seed_coordinate
#print axioms three_pairwise_resultants_nonzero
#print axioms even_quadratic_common_root
#print axioms three_discriminants_negative
#print axioms zero_kernel_discriminant_real_image
#print axioms doubling_not_distance_preserving
end Erdos213.OffsetCircle
