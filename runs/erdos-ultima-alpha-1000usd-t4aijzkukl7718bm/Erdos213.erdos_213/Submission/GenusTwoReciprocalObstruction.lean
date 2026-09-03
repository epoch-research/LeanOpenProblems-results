import FormalConjecturesUtil

/-! Arithmetic obstructions for a restricted reciprocal genus-two construction.
These are not restrictions on arbitrary rational-distance point sets. -/
namespace Erdos213.GenusTwoReciprocalObstruction

private lemma squares_mod_three : ∀ x y : ZMod 3, x^2+y^2=0 → x=0 ∧ y=0 := by
  decide

lemma integer_divisibility {x y a b : ℤ}
    (ha : a^2=x^2+y^2) (hb : b^2=6*x*y-x^2-y^2) :
    (3 : ℤ) ∣ x ∧ (3 : ℤ) ∣ y := by
  have h1 : (a : ZMod 3)^2=(x : ZMod 3)^2+(y : ZMod 3)^2 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ZMod 3)) ha
  have h2 : (b : ZMod 3)^2=6*(x : ZMod 3)*(y : ZMod 3)-(x : ZMod 3)^2-(y : ZMod 3)^2 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ZMod 3)) hb
  have hab : (a : ZMod 3)^2+(b : ZMod 3)^2=0 := by
    rw [show (6 : ZMod 3)=0 by decide] at h2
    linear_combination h1+h2
  have hz := (squares_mod_three _ _ hab).1
  have hxy : (x : ZMod 3)^2+(y : ZMod 3)^2=0 := by simpa [hz] using h1.symm
  have hh := squares_mod_three _ _ hxy
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd x 3).mp hh.1,
    (ZMod.intCast_zmod_eq_zero_iff_dvd y 3).mp hh.2⟩

/-- This simultaneous rational-square system has no solution, including at
zero. The proof uses primitive numerator and denominator modulo three. -/
theorem no_simultaneous_squares (r : ℚ) :
    ¬ (IsSquare (r^2+1) ∧ IsSquare (6*r-r^2-1)) := by
  rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
  have hd : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hn : (r.num : ℚ)=r*(r.den : ℚ) := by
    calc
      _=((r.num : ℚ)/(r.den : ℚ))*(r.den : ℚ) := by field_simp
      _=_ := by rw [Rat.num_div_den]
  have hA : IsSquare ((r.num^2+(r.den : ℤ)^2 : ℤ) : ℚ) := by
    refine ⟨a*(r.den : ℚ),?_⟩
    push_cast
    rw [hn]
    linear_combination (r.den : ℚ)^2*ha
  have hB : IsSquare ((6*r.num*(r.den : ℤ)-r.num^2-(r.den : ℤ)^2 : ℤ) : ℚ) := by
    refine ⟨b*(r.den : ℚ),?_⟩
    push_cast
    rw [hn]
    linear_combination (r.den : ℚ)^2*hb
  obtain ⟨A,hA⟩ := Rat.isSquare_intCast_iff.mp hA
  obtain ⟨B,hB⟩ := Rat.isSquare_intCast_iff.mp hB
  have hdiv := integer_divisibility (by simpa only [pow_two] using hA.symm)
    (by simpa only [pow_two] using hB.symm)
  obtain ⟨u,v,huv⟩ := r.isCoprime_num_den
  have hbad : (3 : ℤ) ∣ 1 := by
    rw [← huv]
    exact dvd_add (dvd_mul_of_dvd_right hdiv.1 u) (dvd_mul_of_dvd_right hdiv.2 v)
  norm_num at hbad

/-- Discriminant of the unit-norm quadratic obtained by translating by
both negative reciprocal branch roots. -/
def translatedDiscriminant (r : ℚ) : ℚ := (r+1/r-4)^2-4

lemma discriminant_identity {r : ℚ} (hr : r ≠ 0) :
    -translatedDiscriminant r=((r-1)/r)^2*(6*r-r^2-1) := by
  unfold translatedDiscriminant
  field_simp
  ring

/-- Rational branch distances rule out aligning this translated quadratic
with the imaginary quadratic field of the source U=X²+1. -/
theorem translated_field_not_aligned {r : ℚ} (hr : r ≠ 0)
    (hbranch : IsSquare (r^2+1)) : ¬ IsSquare (-translatedDiscriminant r) := by
  intro h
  have hr1 : r ≠ 1 := by
    intro he
    subst r
    norm_num at hbranch
  rw [discriminant_identity hr] at h
  obtain ⟨d,hd⟩ := h
  apply no_simultaneous_squares r
  refine ⟨hbranch,⟨d*r/(r-1),?_⟩⟩
  have hrm : r-1 ≠ 0 := sub_ne_zero.mpr hr1
  field_simp at hd ⊢
  nlinarith [hd]

/-- A polynomial certificate for the translated quadratic. This certifies
only the factor identity, not a general Jacobian-to-distance construction. -/
lemma translation_identity {r : ℚ} (hr : r ≠ 0) (x : ℚ) :
    2*x*(x^2-r^2)*(x^2-(1/r)^2)-
      (-(r+x)*(x-1)*(r*x+1)/r)^2 =
    -(x^2+1)*(x+r)*(x+1/r)*(x^2+(r+1/r-4)*x+1) := by
  field_simp
  ring

private def norm47 (p q : ℚ × ℚ) : ℚ := (p.1-q.1)^2+47*(p.2-q.2)^2
private def pointA : ℚ × ℚ := (19/192,5/192)
private def pointB (s : Bool) : ℚ × ℚ := (23/24,if s then 1/24 else -1/24)
private def pointC (s : Bool) : ℚ × ℚ := (19/8,if s then 5/8 else -5/8)

lemma seed_squared_distances :
    norm47 pointA (pointB true)=3/4 ∧
    norm47 pointA (pointC true)=529/24 ∧
    norm47 (pointB true) (pointC true)=18 := by
  norm_num [norm47,pointA,pointB,pointC]

private lemma scale_implies_square_ratio {r s : ℚ} {l : ℝ} (hr : r ≠ 0) (hl : l ≠ 0)
    {a b : ℚ} (ha : l*(r : ℝ)=(a : ℝ)^2) (hb : l*(s : ℝ)=(b : ℝ)^2) :
    IsSquare (s/r) := by
  have ha0 : a ≠ 0 := by
    intro h
    subst a
    simp only [Rat.cast_zero,zero_pow (by decide : 2 ≠ 0)] at ha
    exact (mul_ne_zero hl (by exact_mod_cast hr)) ha
  have hc : s*a^2=r*b^2 := by
    have he : (s : ℝ)*(a : ℝ)^2=(r : ℝ)*(b : ℝ)^2 := by
      linear_combination (r : ℝ)*hb-(s : ℝ)*ha
    exact_mod_cast he
  refine ⟨b/a,?_⟩
  field_simp
  nlinarith [hc]

/-- For every choice of conjugate roots in the three common-field
representatives of the control, even their two B-incident edges cannot
simultaneously acquire rational lengths under a common nonzero scale.
The parameter l is the square of a geometric scale. -/
theorem seed_no_common_scale (s t : Bool) (l : ℝ) (hl : l ≠ 0) :
    ¬ ∃ a b : ℚ,
      l*(norm47 pointA (pointB s) : ℝ)=(a : ℝ)^2 ∧
      l*(norm47 (pointB s) (pointC t) : ℝ)=(b : ℝ)^2 := by
  rintro ⟨a,b,ha,hb⟩
  have hn : norm47 pointA (pointB s) ≠ 0 := by
    cases s <;> norm_num [norm47,pointA,pointB]
  have he := scale_implies_square_ratio hn hl ha hb
  cases s <;> cases t <;>
    norm_num [norm47,pointA,pointB,pointC,Rat.isSquare_iff] at he

#print axioms integer_divisibility
#print axioms no_simultaneous_squares
#print axioms translated_field_not_aligned
#print axioms translation_identity
#print axioms seed_squared_distances
#print axioms seed_no_common_scale
end Erdos213.GenusTwoReciprocalObstruction
