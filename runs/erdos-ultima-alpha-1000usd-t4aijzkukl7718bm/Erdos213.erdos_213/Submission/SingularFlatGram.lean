import Submission.FermatArea

/-! A singular flat-Gram parametrization and a restricted arithmetic
obstruction. No all-distance octad or Erdős-213 settlement is asserted. -/
namespace Erdos213.SingularFlatGram
set_option maxHeartbeats 2000000

variable (p q r t : ℚ)
def diagA (_p q r t : ℚ) : ℚ := -q^2/t+r^2/(1+t)
def diagB (p _q r t : ℚ) : ℚ := -p^2*t+r^2*t/(1+t)
def diagC (p q _r t : ℚ) : ℚ := p^2*(1+t)+q^2*(1+t)/t
def gramDet (A B C d e f : ℚ) : ℚ :=
  A*B*C+2*d*e*f-A*f^2-B*e^2-C*d^2

theorem trace_eq (ht : t≠0) (ht1 : 1+t≠0) :
    diagA p q r t+diagB p q r t+diagC p q r t=p^2+q^2+r^2 := by
  dsimp [diagA,diagB,diagC]
  field_simp
  ring

theorem determinant_zero (ht : t≠0) (ht1 : 1+t≠0) :
    gramDet (diagA p q r t) (diagB p q r t) (diagC p q r t)
      (p*q) (p*r) (q*r)=0 := by
  dsimp [gramDet,diagA,diagB,diagC]
  field_simp
  ring

def bodyNorm (i : Fin 4) : ℚ :=
  let S := diagA p q r t+diagB p q r t+diagC p q r t
  ![S+2*p*q+2*p*r+2*q*r,S+2*p*q-2*p*r-2*q*r,
    S-2*p*q+2*p*r-2*q*r,S-2*p*q-2*p*r+2*q*r] i

theorem four_body_squares (ht : t≠0) (ht1 : 1+t≠0) (i : Fin 4) :
    bodyNorm p q r t i=(![(p+q+r)^2,(p+q-r)^2,(p-q+r)^2,(p-q-r)^2] i) := by
  unfold bodyNorm
  rw [trace_eq p q r t ht ht1]
  fin_cases i <;> dsimp <;> ring

/-- A rank-zero elliptic obstruction in a reciprocal coordinate. -/
lemma inverse_pair_collapse {x a b : ℚ} (hx : x≠0)
    (ha : a^2=2-x-1/x) (hb : b^2=6-x-1/x) : a=0 := by
  by_contra ha0
  have hax : a^2*x= -(x-1)^2 := by
    field_simp at ha
    nlinarith only [ha]
  have hbx : b^2*x=6*x-x^2-1 := by
    field_simp at hb
    nlinarith only [hb]
  let z : ℚ := (x-1)/a
  have hz : z^2= -x := by
    dsimp [z]
    field_simp
    nlinarith only [hax]
  have hz0 : z≠0 := by
    intro h
    rw [h] at hz
    exact hx (by linarith)
  apply FermatArea.quartic_not_square hz0
  refine ⟨z*b, ?_⟩
  have hxz : x= -z^2 := by linarith only [hz]
  rw [hxz] at hbx
  nlinarith only [hbx]

/-- When one face branch degenerates by `r²=4pq`, the two rational face
lengths force a zero face. This is not an obstruction to other parameters. -/
theorem face_branch_collapse {p q r t : ℚ}
    (hp : p≠0) (hq : q≠0) (ht : t≠0) (hr : r^2=4*p*q)
    (hplus : IsSquare (r^2-p^2*t-q^2/t+2*p*q))
    (hminus : IsSquare (r^2-p^2*t-q^2/t-2*p*q)) :
    r^2-p^2*t-q^2/t-2*p*q=0 := by
  have hr0 : r≠0 := by
    intro hz
    rw [hz] at hr
    have h := mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℚ)≠0) hp) hq
    apply h
    nlinarith only [hr]
  obtain ⟨a,ha⟩ := hminus
  obtain ⟨b,hb⟩ := hplus
  have hx0 : p*t/q≠0 := div_ne_zero (mul_ne_zero hp ht) hq
  have hA : (2*a/r)^2=2-(p*t/q)-1/(p*t/q) := by
    field_simp at ha ⊢
    rw [hr] at ha ⊢
    linear_combination -4*p*q*ha
  have hB : (2*b/r)^2=6-(p*t/q)-1/(p*t/q) := by
    field_simp at hb ⊢
    rw [hr] at hb ⊢
    linear_combination -4*p*q*hb
  have hz := inverse_pair_collapse hx0 hA hB
  have ha0 : a=0 := by
    have hh := (div_eq_zero_iff.mp hz).resolve_right hr0
    nlinarith only [hh]
  simpa only [ha0,mul_zero] using ha

theorem face_branch_collapse_negative {p q r t : ℚ}
    (hp : p≠0) (hq : q≠0) (ht : t≠0) (hr : r^2= -4*p*q)
    (hplus : IsSquare (r^2-p^2*t-q^2/t+2*p*q))
    (hminus : IsSquare (r^2-p^2*t-q^2/t-2*p*q)) :
    r^2-p^2*t-q^2/t+2*p*q=0 := by
  have hr' : r^2=4*p*(-q) := by nlinarith only [hr]
  have hp' : IsSquare (r^2-p^2*t-(-q)^2/t+2*p*(-q)) := by
    convert hminus using 1
    ring
  have hm' : IsSquare (r^2-p^2*t-(-q)^2/t-2*p*(-q)) := by
    convert hplus using 1
    ring
  simpa only [neg_sq,mul_neg,sub_neg_eq_add] using
    face_branch_collapse hp (neg_ne_zero.mpr hq) ht hr' hp' hm'

lemma two_face_identity (ht : t≠0) (ht1 : 1+t≠0) :
    diagA p q r t+diagB p q r t=r^2-p^2*t-q^2/t := by
  dsimp [diagA,diagB]
  field_simp
  ring

/-- Neither sign of the quadratic-discriminant collapse can occur with
both rational face lengths and a positive two-dimensional Gram minor. -/
theorem no_positive_face_branch {p q r t : ℚ}
    (hp : p≠0) (hq : q≠0) (ht : t≠0) (ht1 : 1+t≠0)
    (hr : r^2=4*p*q ∨ r^2= -4*p*q)
    (hminor : 0<diagA p q r t*diagB p q r t-(p*q)^2)
    (hplus : IsSquare (diagA p q r t+diagB p q r t+2*p*q))
    (hminus : IsSquare (diagA p q r t+diagB p q r t-2*p*q)) : False := by
  have he := two_face_identity p q r t ht ht1
  rw [he] at hplus hminus
  rcases hr with hr | hr
  · have hz := face_branch_collapse hp hq ht hr hplus hminus
    rw [← he] at hz
    have hs : diagA p q r t+diagB p q r t=2*p*q := by linarith only [hz]
    have hs2 := congrArg (fun z : ℚ => z^2) hs
    nlinarith only [hs2,hminor,sq_nonneg (diagA p q r t-diagB p q r t)]
  · have hz := face_branch_collapse_negative hp hq ht hr hplus hminus
    rw [← he] at hz
    have hs : diagA p q r t+diagB p q r t= -2*p*q := by linarith only [hz]
    have hs2 := congrArg (fun z : ℚ => z^2) hs
    nlinarith only [hs2,hminor,sq_nonneg (diagA p q r t-diagB p q r t)]

#print axioms trace_eq
#print axioms determinant_zero
#print axioms four_body_squares
#print axioms inverse_pair_collapse
#print axioms face_branch_collapse
#print axioms no_positive_face_branch
end Erdos213.SingularFlatGram
