import FormalConjecturesUtil

/-! A universal four-to-four rational-distance transformation. It does not
increase cardinality. A cyclic input forces three outputs onto a line, so
this is not a general-position growth construction for Erdős 213. -/
namespace Erdos213.SquaredBimedians
open EuclideanGeometry
noncomputable section
set_option maxHeartbeats 3000000

def Rational (x : ℝ) : Prop := ∃ q : ℚ, (q : ℝ) = x

lemma Rational.add {x y : ℝ} (hx : Rational x) (hy : Rational y) : Rational (x+y) := by
  obtain ⟨q,rfl⟩ := hx
  obtain ⟨r,rfl⟩ := hy
  exact ⟨q+r,by simp⟩
lemma Rational.sub {x y : ℝ} (hx : Rational x) (hy : Rational y) : Rational (x-y) := by
  obtain ⟨q,rfl⟩ := hx
  obtain ⟨r,rfl⟩ := hy
  exact ⟨q-r,by simp⟩
lemma Rational.mul {x y : ℝ} (hx : Rational x) (hy : Rational y) : Rational (x*y) := by
  obtain ⟨q,rfl⟩ := hx
  obtain ⟨r,rfl⟩ := hy
  exact ⟨q*r,by simp⟩
lemma Rational.sq {x : ℝ} (hx : Rational x) : Rational (x^2) := by
  simpa only [pow_two] using hx.mul hx

/-- Centering a spiral center at the quadrilateral's centroid makes its
numerator a product of the other two bimedians. This polynomial identity
requires no nonzero-denominator assumption. -/
lemma centered_spiral_numerator (a b c d : ℂ) :
    4*(a*c-b*d)-(a+b+c+d)*(a+c-b-d)=
      -(a+b-c-d)*(a+d-b-c) := by ring

lemma bimedian_norm_sq (a b c d : ℂ) :
    ‖a+c-b-d‖^2 = dist a b^2+dist a d^2+dist c b^2+dist c d^2-
      dist a c^2-dist b d^2 := by
  simp only [dist_eq_norm, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

lemma square_bimedian_rational (a b c d : ℂ)
    (hab : Rational (dist a b)) (hac : Rational (dist a c))
    (had : Rational (dist a d)) (hbc : Rational (dist b c))
    (hbd : Rational (dist b d)) (hcd : Rational (dist c d)) :
    Rational ‖(a+c-b-d)^2‖ := by
  rw [norm_pow, bimedian_norm_sq]
  have hcb : Rational (dist c b) := by simpa only [dist_comm] using hbc
  exact ((((hab.sq.add had.sq).add hcb.sq).add hcd.sq).sub hac.sq).sub hbd.sq

lemma difference12 (a b c d : ℂ) :
    (a+c-b-d)^2-(a+b-c-d)^2=4*(c-b)*(a-d) := by ring
lemma difference13 (a b c d : ℂ) :
    (a+c-b-d)^2-(a+d-b-c)^2=4*(c-d)*(a-b) := by ring
lemma difference23 (a b c d : ℂ) :
    (a+b-c-d)^2-(a+d-b-c)^2=4*(b-d)*(a-c) := by ring

lemma distance12 (a b c d : ℂ) :
    dist ((a+c-b-d)^2) ((a+b-c-d)^2)=4*dist c b*dist a d := by
  rw [dist_eq_norm,difference12,norm_mul,norm_mul]
  norm_num [dist_eq_norm]
lemma distance13 (a b c d : ℂ) :
    dist ((a+c-b-d)^2) ((a+d-b-c)^2)=4*dist c d*dist a b := by
  rw [dist_eq_norm,difference13,norm_mul,norm_mul]
  norm_num [dist_eq_norm]
lemma distance23 (a b c d : ℂ) :
    dist ((a+b-c-d)^2) ((a+d-b-c)^2)=4*dist b d*dist a c := by
  rw [dist_eq_norm,difference23,norm_mul,norm_mul]
  norm_num [dist_eq_norm]

def output (a b c d : ℂ) : Fin 4 → ℂ :=
  ![0,(a+c-b-d)^2,(a+b-c-d)^2,(a+d-b-c)^2]

/-- Every rational-distance quadrilateral gives four terms with rational
mutual distances. Distinctness and general position are not asserted. -/
theorem rational_four (a b c d : ℂ)
    (hab : Rational (dist a b)) (hac : Rational (dist a c))
    (had : Rational (dist a d)) (hbc : Rational (dist b c))
    (hbd : Rational (dist b d)) (hcd : Rational (dist c d)) :
    ∀ i j, Rational (dist (output a b c d i) (output a b c d j)) := by
  have hcb : Rational (dist c b) := by simpa only [dist_comm] using hbc
  have hdc : Rational (dist d c) := by simpa only [dist_comm] using hcd
  have hdb : Rational (dist d b) := by simpa only [dist_comm] using hbd
  have h01 := square_bimedian_rational a b c d hab hac had hbc hbd hcd
  have h02 := square_bimedian_rational a c b d hac hab had hcb hcd hbd
  have h03 := square_bimedian_rational a b d c hab had hac hbd hbc hdc
  have h4 : Rational 4 := ⟨4,by norm_num⟩
  have h0 : Rational 0 := ⟨0,by norm_num⟩
  have h12 : Rational (dist ((a+c-b-d)^2) ((a+b-c-d)^2)) := by
    rw [distance12]; exact (h4.mul hcb).mul had
  have h13 : Rational (dist ((a+c-b-d)^2) ((a+d-b-c)^2)) := by
    rw [distance13]; exact (h4.mul hcd).mul hab
  have h23 : Rational (dist ((a+b-c-d)^2) ((a+d-b-c)^2)) := by
    rw [distance23]; exact (h4.mul hbd).mul hac
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [output,dist_comm]

def cross (z w : ℂ) : ℝ := z.re*w.im-z.im*w.re

def circleExpr (a b c d : ℂ) : ℝ :=
  Complex.normSq (b-a)*cross (c-a) (d-a)-
    Complex.normSq (c-a)*cross (b-a) (d-a)+
      Complex.normSq (d-a)*cross (b-a) (c-a)

lemma circleExpr_zero {a b c d : ℂ} (h : Cospherical {a,b,c,d}) :
    circleExpr a b c d=0 := by
  obtain ⟨o,r,ho⟩ := h
  have ha := congrArg (fun t : ℝ => t^2) (ho a (by simp))
  have hb := congrArg (fun t : ℝ => t^2) (ho b (by simp))
  have hc := congrArg (fun t : ℝ => t^2) (ho c (by simp))
  have hd := congrArg (fun t : ℝ => t^2) (ho d (by simp))
  simp only [dist_eq_norm, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re,Complex.sub_im] at ha hb hc hd
  unfold circleExpr cross
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
  linear_combination
    ((c.re-a.re)*(d.im-a.im)-(c.im-a.im)*(d.re-a.re))*(hb-ha)-
    ((b.re-a.re)*(d.im-a.im)-(b.im-a.im)*(d.re-a.re))*(hc-ha)+
    ((b.re-a.re)*(c.im-a.im)-(b.im-a.im)*(c.re-a.re))*(hd-ha)

lemma bimedian_cross (a b c d : ℂ) :
    cross ((a+b-c-d)^2-(a+c-b-d)^2)
      ((a+d-b-c)^2-(a+c-b-d)^2)=16*circleExpr a b c d := by
  simp only [cross,circleExpr,Complex.normSq_apply,pow_two,
    Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im]
  ring

private lemma dependent {z w : ℂ} (hz : z≠0) (h : cross z w=0) :
    ∃ r : ℝ, w=r • z := by
  unfold cross at h
  by_cases hx : z.re=0
  · have hy : z.im≠0 := by
      intro hh
      exact hz (Complex.ext hx hh)
    have hw : w.re=0 := by
      rw [hx,zero_mul,zero_sub,neg_eq_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hy
    refine ⟨w.im/z.im,?_⟩
    apply Complex.ext
    · simp [hx,hw]
    · simp [hy]
  · refine ⟨w.re/z.re,?_⟩
    apply Complex.ext
    · simp [hx]
    · simp only [Complex.smul_im,smul_eq_mul]
      field_simp
      nlinarith only [h]

lemma collinear_of_cross (a b c : ℂ) (h : cross (b-a) (c-a)=0) :
    Collinear ℝ {a,b,c} := by
  by_cases hb : b=a
  · subst b
    simpa using collinear_pair ℝ a c
  obtain ⟨r,hr⟩ := dependent (sub_ne_zero.mpr hb) h
  apply (collinear_iff_of_mem (by simp : a∈({a,b,c} : Set ℂ))).mpr
  refine ⟨b-a,?_⟩
  intro p hp
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0,by simp⟩
  · exact ⟨1,by simp⟩
  · refine ⟨r,?_⟩
    simpa using sub_eq_iff_eq_add.mp hr

/-- For every cyclic source, the three squared bimedians are collinear.
This is independent of rationality and allows all degeneracies. -/
theorem cyclic_outputs_collinear {a b c d : ℂ} (h : Cospherical {a,b,c,d}) :
    Collinear ℝ {(a+c-b-d)^2,(a+b-c-d)^2,(a+d-b-c)^2} := by
  apply collinear_of_cross
  rw [bimedian_cross,circleExpr_zero h,mul_zero]

#print axioms rational_four
#print axioms cyclic_outputs_collinear
end
end Erdos213.SquaredBimedians
