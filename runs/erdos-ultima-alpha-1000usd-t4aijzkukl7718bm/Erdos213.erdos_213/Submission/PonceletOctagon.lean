import Submission.FermatArea

/-! An obstruction for a Jacobi eight-step conic family, NOT for arbitrary
integral-distance sets. All variables below are rational. -/
namespace Erdos213.PonceletOctagon

def den (q s : ℚ) : ℚ := 1-(1-q^2)*s^2
def num (q r s : ℚ) : ℚ := 1+2*r^2*(q-1)*s^2+r^2*(q-1)^2*s^4
def stepS (q r s c d : ℚ) : ℚ := (q^2*s+c*d)/(r*den q s)
def stepC (q r s c d : ℚ) : ℚ := q*(c-s*d)/(r*den q s)
def stepD (q s c d : ℚ) : ℚ := q*(d-(1-q^2)*s*c)/den q s
def radiusSq (B s c : ℚ) : ℚ := c^2+B*s^2

lemma step_circle (q r s c d : ℚ) (hr : r^2=1+q^2)
    (hc : c^2+s^2=1) (hd : d^2+(1-q^4)*s^2=1)
    (hr0 : r ≠ 0) (hD : den q s ≠ 0) :
    (stepC q r s c d)^2+(stepS q r s c d)^2=1 := by
  dsimp [stepC,stepS]
  field_simp
  dsimp [den]
  linear_combination (-s^4*q^4 + 2*s^4*q^2 - s^4 - 2*s^2*q^2 + 2*s^2 - 1) * hr + (c^2 + s^2*q^2) * hd + (s^2*q^4 - s^2 + q^2 + 1) * hc

lemma step_dn (q r s c d : ℚ) (hr : r^2=1+q^2)
    (hc : c^2+s^2=1) (hd : d^2+(1-q^4)*s^2=1)
    (hr0 : r ≠ 0) (hD : den q s ≠ 0) :
    (stepD q s c d)^2+(1-q^4)*(stepS q r s c d)^2=1 := by
  dsimp [stepD,stepS]
  field_simp
  dsimp [den]
  linear_combination (d^2*q^2 + 2*d*c*s*q^4 - 2*d*c*s*q^2 + c^2*s^2*q^6 - 2*c^2*s^2*q^4 + c^2*s^2*q^2 - s^4*q^4 + 2*s^4*q^2 - s^4 - 2*s^2*q^2 + 2*s^2 - 1) * hr + (-c^2*q^4 + c^2 + q^4 + q^2) * hd + (-s^2*q^6 + s^2*q^4 + s^2*q^2 - s^2 - q^4 + 1) * hc

lemma step_sc_poly (q r s c d : ℚ) (hr : r^2=1+q^2)
    (hc : c^2+s^2=1) (hd : d^2+(1-q^4)*s^2=1) :
    (q^2*s+c*d)*(c-s*d) =
      (1-r^2*s^2)*(d-(1-q^2)*s*c) := by
  linear_combination (d*s^2 + c*s^3*q^2 - c*s^3) * hr + (-c*s) * hd + (d) * hc

lemma step_sc (q r s c d : ℚ) (hr : r^2=1+q^2)
    (hc : c^2+s^2=1) (hd : d^2+(1-q^4)*s^2=1)
    (hq0 : q ≠ 0) (hr0 : r ≠ 0) (hD : den q s ≠ 0)
    (he : d-(1-q^2)*s*c ≠ 0) :
    stepS q r s c d * stepC q r s c d / stepD q s c d =
      (1-r^2*s^2)/(r^2*den q s) := by
  have h := step_sc_poly q r s c d hr hc hd
  have he' : q^2*s*c-s*c+d ≠ 0 := by convert he using 1; ring
  calc
    _ = ((q^2*s+c*d)*(c-s*d))/((r^2*den q s)*(d-(1-q^2)*s*c)) := by
      dsimp [stepS,stepC,stepD]
      field_simp [he,he']
    _ = _ := by rw [h]; exact mul_div_mul_right _ _ he

lemma norm_pair_poly (q r B s c d : ℚ) (hr : r^2=1+q^2)
    (hc : c^2+s^2=1) (hd : d^2+(1-q^4)*s^2=1)
    (hB : B^2-2*q*(q^2-q+1)*B+q^4=0) :
    (c^2+B*s^2)*(q^4*s^2+B*c^2) =
      B*(d^2-r^2*(q-1)^2*s^2*c^2) := by
  linear_combination (c^2*B*s^2*q^2 - 2*c^2*B*s^2*q + c^2*B*s^2) * hr + (-B) * hd + (c^2*B + B^2*s^2 + B*s^2*q^4 - 2*B*s^2*q^3 + 2*B*s^2*q^2 - 2*B*s^2*q + B + s^2*q^4) * hc + (-s^4 + s^2) * hB

lemma norm_numerator (q r s c d : ℚ) (hr : r^2=1+q^2)
    (hc : c^2+s^2=1) (hd : d^2+(1-q^4)*s^2=1) :
    d^2-r^2*(q-1)^2*s^2*c^2=num q r s := by
  dsimp [num]
  linear_combination (-c^2*s^2*q^2 + 2*c^2*s^2*q - c^2*s^2 - s^4*q^2 + 2*s^4*q - s^4 - 2*s^2*q + 2*s^2) * hr + (1) * hd + (-s^2*q^4 + 2*s^2*q^3 - 2*s^2*q^2 + 2*s^2*q - s^2) * hc

lemma complement_poly (q r s : ℚ) (hr : r^2=1+q^2) :
    r^2*(den q s)^2-(q-1)^2*(1-r^2*s^2)^2=2*q*num q r s := by
  dsimp [den,num]
  linear_combination (-r^2*s^4*q^2 + 2*r^2*s^4*q - r^2*s^4 + 1) * hr

lemma norm_pair (q r B s c d : ℚ) (hr : r^2=1+q^2)
    (hc : c^2+s^2=1) (hd : d^2+(1-q^4)*s^2=1)
    (hB : B^2-2*q*(q^2-q+1)*B+q^4=0) (hd0 : d ≠ 0) :
    radiusSq B s c * radiusSq B (c/d) (-q^2*s/d) =
      B*(1-r^2*(q-1)^2*(s*c/d)^2) := by
  have h := norm_pair_poly q r B s c d hr hc hd hB
  dsimp [radiusSq]
  field_simp
  linear_combination h

lemma norm_pair_first (q r B s c d : ℚ) (hr : r^2=1+q^2)
    (hc : c^2+s^2=1) (hd : d^2+(1-q^4)*s^2=1)
    (hB : B^2-2*q*(q^2-q+1)*B+q^4=0) (hd0 : d ≠ 0) :
    radiusSq B s c * radiusSq B (c/d) (-q^2*s/d) = B*num q r s/d^2 := by
  rw [norm_pair q r B s c d hr hc hd hB hd0]
  have h := norm_numerator q r s c d hr hc hd
  field_simp
  linear_combination B*h

lemma twice_not_square (q r : ℚ) (hq : 0<q) (hr : r^2=1+q^2) :
    ¬ IsSquare (2*q) := by
  rintro ⟨z,hz⟩
  have hr0 : r ≠ 0 := by intro h; rw [h] at hr; nlinarith only [hr,sq_nonneg q]
  apply FermatArea.no_rational_square_area (x := 1) (y := q) (z := |r|)
    (by norm_num) hq (abs_pos.mpr hr0)
    (by rw [sq_abs]; nlinarith only [hr])
  refine ⟨z/2,?_⟩
  linear_combination hz/4

lemma four_radii_identity (q r B s c d : ℚ) (hr : r^2=1+q^2)
    (hc : c^2+s^2=1) (hd : d^2+(1-q^4)*s^2=1)
    (hB : B^2-2*q*(q^2-q+1)*B+q^4=0)
    (hq0 : q ≠ 0) (hr0 : r ≠ 0) (hd0 : d ≠ 0) (hD : den q s ≠ 0)
    (he : d-(1-q^2)*s*c ≠ 0) :
    radiusSq B s c * radiusSq B (c/d) (-q^2*s/d) *
      radiusSq B (stepS q r s c d) (stepC q r s c d) *
      radiusSq B (stepC q r s c d / stepD q s c d)
        (-q^2*stepS q r s c d / stepD q s c d) =
    2*q*(B*num q r s/(r*d*den q s))^2 := by
  have hc1 := step_circle q r s c d hr hc hd hr0 hD
  have hd1 := step_dn q r s c d hr hc hd hr0 hD
  have hd10 : stepD q s c d ≠ 0 := div_ne_zero (mul_ne_zero hq0 he) hD
  have h0 := norm_pair_first q r B s c d hr hc hd hB hd0
  have h1 := norm_pair q r B (stepS q r s c d) (stepC q r s c d)
    (stepD q s c d) hr hc1 hd1 hB hd10
  rw [step_sc q r s c d hr hc hd hq0 hr0 hD he] at h1
  have hcomp : B*(1-r^2*(q-1)^2*((1-r^2*s^2)/(r^2*den q s))^2) =
      2*q*B*num q r s/(r^2*(den q s)^2) := by
    have h := complement_poly q r s hr
    field_simp
    linear_combination B*h
  rw [hcomp] at h1
  calc
    _ = (radiusSq B s c * radiusSq B (c/d) (-q^2*s/d)) *
        (radiusSq B (stepS q r s c d) (stepC q r s c d) *
        radiusSq B (stepC q r s c d / stepD q s c d)
          (-q^2*stepS q r s c d / stepD q s c d)) := by ring
    _ = (B*num q r s/d^2)*(2*q*B*num q r s/(r^2*(den q s)^2)) := by rw [h0,h1]
    _ = _ := by field_simp

lemma num_pos (q r B s c d : ℚ) (hr : r^2=1+q^2)
    (hc : c^2+s^2=1) (hd : d^2+(1-q^4)*s^2=1)
    (hB : B^2-2*q*(q^2-q+1)*B+q^4=0) (hq0 : q ≠ 0) (hBp : 0<B) :
    0<num q r s := by
  have h0 : 0<c^2+B*s^2 := by
    by_cases hcz : c=0
    · have hs : s^2=1 := by simpa [hcz] using hc
      simpa [hcz,hs] using hBp
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hcz)
        (mul_nonneg (le_of_lt hBp) (sq_nonneg s))
  have h2 : 0<q^4*s^2+B*c^2 := by
    by_cases hsz : s=0
    · have hcc : c^2=1 := by simpa [hsz] using hc
      simpa [hsz,hcc] using hBp
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (pow_pos (sq_pos_of_ne_zero hq0) 2 |>.trans_eq (by ring))
          (sq_pos_of_ne_zero hsz))
        (mul_nonneg (le_of_lt hBp) (sq_nonneg c))
  have hh := norm_pair_poly q r B s c d hr hc hd hB
  rw [norm_numerator q r s c d hr hc hd] at hh
  have hpos : 0<B*num q r s := hh ▸ mul_pos h0 h2
  nlinarith only [hpos,hBp]

/-- Even a common square class for the four radii is impossible in this
nondegenerate positive-aspect family. This is not a bound for general sets. -/
lemma four_radii_not_square (q r B s c d : ℚ) (hq : 0<q) (hBp : 0<B)
    (hr : r^2=1+q^2) (hc : c^2+s^2=1) (hd : d^2+(1-q^4)*s^2=1)
    (hB : B^2-2*q*(q^2-q+1)*B+q^4=0)
    (hr0 : r ≠ 0) (hd0 : d ≠ 0) (hD : den q s ≠ 0)
    (he : d-(1-q^2)*s*c ≠ 0) :
    ¬ IsSquare (radiusSq B s c * radiusSq B (c/d) (-q^2*s/d) *
      radiusSq B (stepS q r s c d) (stepC q r s c d) *
      radiusSq B (stepC q r s c d / stepD q s c d)
        (-q^2*stepS q r s c d / stepD q s c d)) := by
  rw [four_radii_identity q r B s c d hr hc hd hB (ne_of_gt hq) hr0 hd0 hD he]
  let K := B*num q r s/(r*d*den q s)
  have hK : K ≠ 0 := div_ne_zero
    (mul_ne_zero (ne_of_gt hBp) (ne_of_gt (num_pos q r B s c d hr hc hd hB (ne_of_gt hq) hBp)))
    (mul_ne_zero (mul_ne_zero hr0 hd0) hD)
  change ¬ IsSquare (2*q*K^2)
  rintro ⟨z,hz⟩
  apply twice_not_square q r hq hr
  refine ⟨z/K,?_⟩
  field_simp
  linear_combination hz

lemma common_class_product_square (δ a b c d : ℚ) :
    IsSquare ((δ*a^2)*(δ*b^2)*(δ*c^2)*(δ*d^2)) := by
  refine ⟨δ^2*a*b*c*d,?_⟩
  ring

lemma positive_norm (B s c : ℚ) (hB : 0<B) (hc : c^2+s^2=1) :
    0<c^2+B*s^2 := by
  by_cases hcz : c=0
  · have hs : s^2=1 := by simpa [hcz] using hc
    simpa [hcz,hs] using hB
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hcz)
      (mul_nonneg (le_of_lt hB) (sq_nonneg s))

lemma dn_ne_zero (q s c d : ℚ) (hq : q ≠ 0)
    (hc : c^2+s^2=1) (hd : d^2+(1-q^4)*s^2=1) : d ≠ 0 := by
  have hq4 : 0<q^4 := by nlinarith only [sq_pos_of_ne_zero hq, sq_pos_of_ne_zero (pow_ne_zero 2 hq)]
  have hp := positive_norm (q^4) s c hq4 hc
  have he : d^2=c^2+q^4*s^2 := by linear_combination hd-hc
  intro hz
  rw [hz] at he
  nlinarith only [hp,he]

lemma nonzero_data (q r s c d : ℚ) (hq : q ≠ 0) (hr : r^2=1+q^2)
    (hc : c^2+s^2=1) (hd : d^2+(1-q^4)*s^2=1) :
    r ≠ 0 ∧ d ≠ 0 ∧ den q s ≠ 0 ∧ d-(1-q^2)*s*c ≠ 0 := by
  have hr0 : r ≠ 0 := by intro hz; rw [hz] at hr; nlinarith only [hr,sq_nonneg q]
  have hdp : 0<den q s := by
    have hp := positive_norm (q^2) s c (sq_pos_of_ne_zero hq) hc
    have he : den q s=c^2+q^2*s^2 := by dsimp [den]; linear_combination -hc
    exact he ▸ hp
  have hD := ne_of_gt hdp
  refine ⟨hr0,dn_ne_zero q s c d hq hc hd,hD,?_⟩
  have h1 := dn_ne_zero q (stepS q r s c d) (stepC q r s c d)
    (stepD q s c d) hq (step_circle q r s c d hr hc hd hr0 hD)
    (step_dn q r s c d hr hc hd hr0 hD)
  intro hz
  apply h1
  simp [stepD,hz]

/-- None of these four antipodal radii can all be rational after one common
scaling. In particular, the corresponding eight points cannot supply an
integral-distance configuration. No arbitrary-point-set claim is made. -/
theorem no_common_class (q r B s c d : ℚ) (hq : 0<q) (hBp : 0<B)
    (hr : r^2=1+q^2) (hc : c^2+s^2=1) (hd : d^2+(1-q^4)*s^2=1)
    (hB : B^2-2*q*(q^2-q+1)*B+q^4=0) :
    ¬ ∃ δ a b e f : ℚ,
      radiusSq B s c = δ*a^2 ∧
      radiusSq B (c/d) (-q^2*s/d) = δ*b^2 ∧
      radiusSq B (stepS q r s c d) (stepC q r s c d) = δ*e^2 ∧
      radiusSq B (stepC q r s c d / stepD q s c d)
        (-q^2*stepS q r s c d / stepD q s c d) = δ*f^2 := by
  obtain ⟨hr0,hd0,hD,he⟩ := nonzero_data q r s c d (ne_of_gt hq) hr hc hd
  rintro ⟨δ,a,b,e,f,h0,h2,h1,h3⟩
  apply four_radii_not_square q r B s c d hq hBp hr hc hd hB hr0 hd0 hD he
  rw [h0,h2,h1,h3]
  exact common_class_product_square δ a b e f

lemma aspect_roots (q r : ℚ) (hr : r^2=1+q^2) :
    (q*(q^2-q+1-(q-1)*r))^2 -
      2*q*(q^2-q+1)*(q*(q^2-q+1-(q-1)*r))+q^4=0 ∧
    (q*(q^2-q+1+(q-1)*r))^2 -
      2*q*(q^2-q+1)*(q*(q^2-q+1+(q-1)*r))+q^4=0 := by
  constructor <;> linear_combination q^2*(q-1)^2*hr

/-- The algebraic cancellation behind two perfect matchings. The endpoint
weights may be real, not rational. In a centrally symmetric octagon the
matching of paired opposite sides has squared-length product `(a*b)^2`.
A second matching with product n must therefore have square product if both
matchings become rational-length matchings after endpoint reweighting. -/
lemma matching_switching_square (n a b A C : ℚ) (W : ℝ) (hC : C ≠ 0)
    (h1 : (n : ℝ)*W=(A : ℝ)^2)
    (h2 : ((a*b : ℚ) : ℝ)^2*W=(C : ℝ)^2) : IsSquare n := by
  have he : ((n*C^2 : ℚ) : ℝ)=(((A*a*b)^2 : ℚ) : ℝ) := by
    push_cast
    push_cast at h2
    linear_combination ((a : ℝ)*b)^2*h1-(n : ℝ)*h2
  have heq : n*C^2=(A*a*b)^2 := by exact_mod_cast he
  refine ⟨A*a*b/C,?_⟩
  field_simp
  linear_combination heq

lemma matching_switching_obstruction (n a b : ℚ) (hn : ¬ IsSquare n) :
    ¬ ∃ W : ℝ, ∃ A C : ℚ, C ≠ 0 ∧
      (n : ℝ)*W=(A : ℝ)^2 ∧ ((a*b : ℚ) : ℝ)^2*W=(C : ℝ)^2 := by
  rintro ⟨W,A,C,hC,h1,h2⟩
  exact hn (matching_switching_square n a b A C W hC h1 h2)

#print axioms step_circle
#print axioms step_dn
#print axioms four_radii_identity
#print axioms four_radii_not_square
#print axioms no_common_class
#print axioms aspect_roots
#print axioms matching_switching_obstruction
end Erdos213.PonceletOctagon
