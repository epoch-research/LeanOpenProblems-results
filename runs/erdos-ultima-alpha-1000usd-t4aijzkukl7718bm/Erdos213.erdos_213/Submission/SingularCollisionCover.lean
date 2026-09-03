import Submission.SingularBranchCollisions

/-! Exact reductions on one surviving collision locus. No assertion of an
all-distance octad, unbounded construction, or unrestricted obstruction. -/
namespace Erdos213.SingularFlatGram
set_option maxHeartbeats 2000000

/-- The negative-six quartic is another form of Fermat's square-area obstruction. -/
lemma negative_six_quartic_not_square {w : ℚ} (hw : w≠0) :
    ¬IsSquare (w^4-6*w^2+1) := by
  rintro ⟨c,hc⟩
  have he : c^2=w^4-6*w^2+1 := by nlinarith only [hc]
  have hwpos := sq_pos_of_ne_zero hw
  have habs := sq_abs c
  have ha : 0<w^2+1+|c| := by positivity
  have hb : 0<w^2+1-|c| := by nlinarith only [he,habs,hwpos,abs_nonneg c]
  have hz : 0<2*|w^2-1| := by
    have hne : w^2-1≠0 := by
      intro hh
      have hsq : w^2=1 := by linarith only [hh]
      have hfour : w^4=1 := by nlinarith only [congrArg (fun z : ℚ => z^2) hsq]
      nlinarith only [he,hsq,hfour,sq_nonneg c]
    exact mul_pos (by norm_num) (abs_pos.mpr hne)
  apply FermatArea.no_rational_square_area ha hb hz
  · nlinarith only [he,habs,sq_abs (w^2-1)]
  · refine ⟨2*w,?_⟩
    nlinarith only [he,habs]

def collisionP (w : ℚ) : ℚ := (w^2-1)/2
def collisionR (w : ℚ) : ℚ := (w^2+1)/(2*w)

theorem collision_parameter_identities (w : ℚ) (hw : w≠0) :
    edgeFaceF (collisionP w) 1 (collisionR w)=0 := by
  dsimp [edgeFaceF,collisionP,collisionR]
  field_simp
  ring

/-- Completeness of the one-collision normalization at nonzero parameters. -/
theorem collision_parameter_complete {p q r : ℚ}
    (hp : p≠0) (hq : q≠0) (hr : r≠0) (hF : edgeFaceF p q r=0) :
    ∃ w : ℚ, w≠0 ∧ w^2≠1 ∧
      p/q=collisionP w ∧ r/q=collisionR w := by
  have hpq : p+q≠0 := by
    intro hz
    have he : p= -q := by linarith only [hz]
    dsimp [edgeFaceF] at hF
    rw [he] at hF
    have hh : r^2*q=0 := by nlinarith only [hF]
    exact (mul_ne_zero (pow_ne_zero 2 hr) hq) hh
  let w := (p+q)/r
  have hw : w≠0 := div_ne_zero hpq hr
  have hquad : q*w^2=2*p+q := by
    change q*((p+q)/r)^2=2*p+q
    dsimp [edgeFaceF] at hF
    field_simp
    linear_combination hF
  have hwp : w^2≠1 := by
    intro he
    rw [he] at hquad
    exact hp (by linarith only [hquad])
  have hP : p/q=collisionP w := by
    dsimp [collisionP]
    field_simp
    linear_combination -hquad
  refine ⟨w,hw,hwp,hP,?_⟩
  change r/q=(w^2+1)/(2*w)
  have hwr : w*r=p+q := by dsimp [w]; field_simp
  field_simp
  linear_combination 2*hwr-hquad

/-- The ratio of the colliding face norm to the edge norm is a conic. -/
theorem collision_face_ratio (w t : ℚ) (hw : w≠0) (ht : t≠0) (ht1 : 1+t≠0) :
    diagA (collisionP w) 1 (collisionR w) t +
      diagB (collisionP w) 1 (collisionR w) t + 2*collisionP w =
    diagA (collisionP w) 1 (collisionR w) t * (1+t)*(1-w^2*t) := by
  dsimp [diagA,diagB,collisionP,collisionR]
  field_simp
  ring

/-- Rational parametrization of the ratio conic, away from t=0. -/
theorem ratio_conic_complete {w t z : ℚ} (hw : w≠0) (ht : t≠0)
    (hz : z^2=(1+t)*(1-w^2*t)) :
    ∃ v : ℚ, t=(1-w^2-2*v)/(v^2+w^2) := by
  let v := (z-1)/t
  have hvz : z=1+v*t := by dsimp [v]; field_simp; ring
  have hden : v^2+w^2≠0 := ne_of_gt (by nlinarith only [sq_nonneg v,sq_pos_of_ne_zero hw])
  refine ⟨v,?_⟩
  have hh : t*((v^2+w^2)*t-(1-w^2-2*v))=0 := by
    rw [hvz] at hz
    linear_combination hz
  have hlin := (mul_eq_zero.mp hh).resolve_left ht
  apply (eq_div_iff hden).mpr
  nlinarith only [hlin]

def tangentDisc (p q r : ℚ) : ℚ := (p^2+q^2-r^2)^2-4*p^2*q^2

lemma collision_discriminant_factor (w : ℚ) (hw : w≠0) :
    tangentDisc (collisionP w) 1 (collisionR w) =
      (((w^2-1)*(w^2+1))/(4*w^2))^2*(w^4-6*w^2+1) := by
  dsimp [tangentDisc,collisionP,collisionR]
  field_simp
  ring

/-- The rank-one boundary has no rational tangent slope on this collision
locus. This is NOT nonexistence of points away from the boundary. -/
theorem collision_discriminant_not_square {w : ℚ} (hw : w≠0) (hw1 : w^2≠1) :
    ¬IsSquare (tangentDisc (collisionP w) 1 (collisionR w)) := by
  rintro ⟨d,hd⟩
  let k := ((w^2-1)*(w^2+1))/(4*w^2)
  have hk : k≠0 := by
    dsimp [k]
    exact div_ne_zero
      (mul_ne_zero (sub_ne_zero.mpr hw1) (ne_of_gt (by positivity)))
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hw))
  have he : k^2*(w^4-6*w^2+1)=d^2 := by
    rw [collision_discriminant_factor w hw] at hd
    change k^2*(w^4-6*w^2+1)=d*d at hd
    nlinarith only [hd]
  apply negative_six_quartic_not_square hw
  refine ⟨d/k,?_⟩
  field_simp
  nlinarith only [he]

theorem collision_no_rational_boundary_slope {w : ℚ}
    (hw : w≠0) (hw1 : w^2≠1) (t : ℚ) :
    (collisionP w)^2*t^2+((collisionP w)^2+1-(collisionR w)^2)*t+1≠0 := by
  intro ht
  apply collision_discriminant_not_square hw hw1
  refine ⟨2*(collisionP w)^2*t+((collisionP w)^2+1-(collisionR w)^2),?_⟩
  dsimp [tangentDisc]
  linear_combination -4*(collisionP w)^2*ht

/-- Two nonzero rational square lengths give the displayed conic parameter.
No conclusion about the other seven square conditions is drawn. -/
theorem two_square_collision_reduction {w t a b : ℚ}
    (hw : w≠0) (ht : t≠0) (ht1 : 1+t≠0) (ha0 : a≠0)
    (ha : diagA (collisionP w) 1 (collisionR w) t=a^2)
    (hb : diagA (collisionP w) 1 (collisionR w) t+
      diagB (collisionP w) 1 (collisionR w) t+2*collisionP w=b^2) :
    ∃ v : ℚ, t=(1-w^2-2*v)/(v^2+w^2) := by
  have he := collision_face_ratio w t hw ht ht1
  rw [hb,ha] at he
  have hz : (b/a)^2=(1+t)*(1-w^2*t) := by
    field_simp
    linear_combination he
  exact ratio_conic_complete hw ht hz

/-- The edge-square equation maps to its elliptic quotient. -/
theorem edge_elliptic_identity {r t a : ℚ} (ht : t≠0) (ht1 : 1+t≠0)
    (ha : a^2= -1/t+r^2/(1+t)) :
    let c := r^2-1
    let x := c*t
    let y := c*a*t*(1+t)
    y^2=x^3+(c-1)*x^2-c*x := by
  dsimp only
  have hh : a^2*t*(1+t)=(r^2-1)*t-1 := by
    field_simp at ha
    linear_combination ha
  linear_combination (r^2-1)^2*t*(1+t)*hh

/-- The positive face-square equation has the PLUS sign in its elliptic
quadratic coefficient; changing that sign would give a different twist. -/
theorem face_elliptic_identity {p r t b : ℚ} (ht : t≠0)
    (hb : b^2=r^2-p^2*t-1/t+2*p) :
    let x := -p^2*t
    let y := p^2*b*t
    y^2=x^3+(2*p+r^2)*x^2+p^2*x := by
  dsimp only
  have hh : b^2*t= -p^2*t^2+(2*p+r^2)*t-1 := by
    field_simp at hb
    linear_combination hb
  linear_combination p^4*t*hh

#print axioms negative_six_quartic_not_square
#print axioms collision_parameter_complete
#print axioms collision_face_ratio
#print axioms ratio_conic_complete
#print axioms collision_discriminant_not_square
#print axioms collision_no_rational_boundary_slope
#print axioms two_square_collision_reduction
#print axioms edge_elliptic_identity
#print axioms face_elliptic_identity
end Erdos213.SingularFlatGram
