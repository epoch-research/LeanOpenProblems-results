import Submission.MedianCoverDescent

/-! Inverting the normalized side map of the degree-five median family over R.
The only real double fiber is the equilateral specialization r^2=3. Rational
side ratios and one rational normalized median therefore force a rational
parameter, without assuming that r^2+9/r^2 is rational. This is not an
existence theorem for the extra-square condition or for an eight-point set. -/
namespace Erdos213.MedianShapeInverse
open MedianCoverDescent
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

def baseDen (r : ℝ) : ℝ := 3*r^4+10*r^2-9
def shapeX (r : ℝ) : ℝ := r*(r^2-3)^2/baseDen r
def shapeY (r : ℝ) : ℝ := (r^4+26*r^2+9)/baseDen r

def inverseDen {R : Type*} [CommRing R] (X Y : R) : R :=
  15*X^2*Y^2+415*X^2*Y-140*X^2-97*Y^4+659*Y^3-1680*Y^2+1916*Y-832

def inverseNum {R : Type*} [CommRing R] (X Y : R) : R :=
  -9*X*(51*X^2*Y-17*X^2+59*Y^3-189*Y^2+228*Y-100)

lemma shape_inverse_identity {r : ℝ} (hd : baseDen r≠0) :
    inverseNum (shapeX r) (shapeY r)=r*inverseDen (shapeX r) (shapeY r) := by
  unfold inverseNum inverseDen shapeX shapeY
  field_simp
  unfold baseDen
  ring

lemma inverse_den_factorization {r : ℝ} (hd : baseDen r≠0) :
    inverseDen (shapeX r) (shapeY r)*(baseDen r)^4 =
      -5184*(r^2-3)^2*(3*r^4-16*r^3+30*r^2+27)*(3*r^4+16*r^3+30*r^2+27) := by
  unfold inverseDen shapeX shapeY
  field_simp
  unfold baseDen
  ring

lemma factors_positive (r : ℝ) :
    0<3*r^4-16*r^3+30*r^2+27 ∧ 0<3*r^4+16*r^3+30*r^2+27 := by
  have hm : 0≤3*r^2-16*r+30 := by nlinarith [sq_nonneg (3*r-8)]
  have hp : 0≤3*r^2+16*r+30 := by nlinarith [sq_nonneg (3*r+8)]
  constructor
  · nlinarith only [mul_nonneg (sq_nonneg r) hm]
  · nlinarith only [mul_nonneg (sq_nonneg r) hp]

lemma inverse_den_ne {r : ℝ} (hd : baseDen r≠0) (hr : r^2≠3) :
    inverseDen (shapeX r) (shapeY r)≠0 := by
  have hh := inverse_den_factorization hd
  have hf := factors_positive r
  intro hz
  rw [hz,zero_mul] at hh
  have hn : -5184*(r^2-3)^2*(3*r^4-16*r^3+30*r^2+27)*
      (3*r^4+16*r^3+30*r^2+27)≠0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero 2 (sub_ne_zero.mpr hr))) (ne_of_gt hf.1)) (ne_of_gt hf.2)
  exact hn hh.symm

lemma base_den_ne_of_shape {r A C : ℝ}
    (hA : realA r=A*realB r) (hC : realC r=C*realB r) : baseDen r≠0 := by
  have hb : realB r=2*baseDen r := by unfold realB baseDen; ring
  intro hz
  rw [hb,hz,mul_zero,mul_zero] at hA hC
  have hp : 0<r^4+26*r^2+9 := by positivity
  simp only [realA,realC] at hA hC
  nlinarith only [hA,hC,hp]

lemma shape_coordinates {r A C : ℝ}
    (hA : realA r=A*realB r) (hC : realC r=C*realB r) :
    shapeX r=A+C ∧ shapeY r=A-C := by
  have hd := base_den_ne_of_shape hA hC
  simp only [realA,realB,realC] at hA hC
  constructor
  · unfold shapeX
    apply (div_eq_iff hd).mpr
    unfold baseDen
    linear_combination (hA+hC)/2
  · unfold shapeY
    apply (div_eq_iff hd).mpr
    unfold baseDen
    linear_combination (hA-hC)/2

lemma shape_at_equilateral {r : ℝ} (hr : r^2=3) :
    realA r=96 ∧ realB r=96 ∧ realC r=-96 ∧ realMedianU r=96*r := by
  refine ⟨?_,?_,?_,?_⟩
  · unfold realA
    linear_combination (r^3+r^2-3*r+29)*hr
  · unfold realB
    linear_combination (6*r^2+38)*hr
  · unfold realC
    linear_combination (r^3-r^2-3*r-29)*hr
  · unfold realMedianU
    linear_combination (r^3+3*r^2+29*r-9)*hr

/-- The normalized side map is injective away from its single real double
fiber. This theorem is over R and has no arithmetic hypotheses. -/
theorem real_side_fibers {r s A C : ℝ}
    (hrA : realA r=A*realB r) (hrC : realC r=C*realB r)
    (hsA : realA s=A*realB s) (hsC : realC s=C*realB s) :
    r=s ∨ (r^2=3 ∧ s^2=3) := by
  have hdr := base_den_ne_of_shape hrA hrC
  have hds := base_den_ne_of_shape hsA hsC
  obtain ⟨hrX,hrY⟩ := shape_coordinates hrA hrC
  obtain ⟨hsX,hsY⟩ := shape_coordinates hsA hsC
  have hir := shape_inverse_identity hdr
  have his := shape_inverse_identity hds
  rw [hrX,hrY] at hir
  rw [hsX,hsY] at his
  by_cases hd : inverseDen (A+C) (A-C)=0
  · right
    constructor
    · by_contra h
      exact inverse_den_ne hdr h (by rwa [hrX,hrY])
    · by_contra h
      exact inverse_den_ne hds h (by rwa [hsX,hsY])
  · left
    exact mul_right_cancel₀ hd (hir.symm.trans his)

/-- No rational reciprocal quotient assumption is needed for rational signed
side ratios: the parameter is rational or the shape is equilateral. -/
theorem rational_parameter_or_equilateral {r : ℝ} {A C : ℚ}
    (hA : realA r=(A : ℝ)*realB r) (hC : realC r=(C : ℝ)*realB r) :
    r∈Set.range ((↑) : ℚ → ℝ) ∨ r^2=3 := by
  by_cases hr : r^2=3
  · exact Or.inr hr
  left
  have hd := base_den_ne_of_shape hA hC
  obtain ⟨hx,hy⟩ := shape_coordinates hA hC
  have hi := shape_inverse_identity hd
  have hn := inverse_den_ne hd hr
  rw [hx,hy] at hi hn
  refine ⟨inverseNum (A+C) (A-C)/inverseDen (A+C) (A-C),?_⟩
  push_cast [inverseNum,inverseDen]
  apply (div_eq_iff ?_).mpr
  · simpa only [inverseNum,inverseDen] using hi
  · simpa only [inverseDen] using hn

/-- One rational normalized median removes the equilateral exception. -/
theorem rational_parameter_of_rational_sides_and_median {r : ℝ} {A C M : ℚ}
    (hA : realA r=(A : ℝ)*realB r) (hC : realC r=(C : ℝ)*realB r)
    (hM : (realMedianU r)^2=(M : ℝ)^2*(realB r)^2) :
    r∈Set.range ((↑) : ℚ → ℝ) := by
  rcases rational_parameter_or_equilateral hA hC with h | h
  · exact h
  · obtain ⟨_,hb,_,hm⟩ := shape_at_equilateral h
    rw [hb,hm] at hM
    have hsR : (M : ℝ)^2=3 := by nlinarith only [h,hM]
    have hs : M^2=3 := by exact_mod_cast hsR
    have hn : ¬IsSquare (3 : ℚ) := by norm_num
    exact False.elim (hn ⟨M,by nlinarith only [hs]⟩)

lemma signed_rational_ratio {x y : ℝ} {A : ℚ}
    (h : x^2=(A : ℝ)^2*y^2) : ∃ a : ℚ, x=(a : ℝ)*y := by
  rw [← mul_pow] at h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact ⟨A,h⟩
  · exact ⟨-A,by simpa only [Rat.cast_neg,neg_mul] using h⟩

/-- The signs of the side polynomials are irrelevant for length data. -/
theorem rational_parameter_of_rational_lengths {r : ℝ} {A C M : ℚ}
    (hA : (realA r)^2=(A : ℝ)^2*(realB r)^2)
    (hC : (realC r)^2=(C : ℝ)^2*(realB r)^2)
    (hM : (realMedianU r)^2=(M : ℝ)^2*(realB r)^2) :
    r∈Set.range ((↑) : ℚ → ℝ) := by
  obtain ⟨a,ha⟩ := signed_rational_ratio hA
  obtain ⟨c,hc⟩ := signed_rational_ratio hC
  exact rational_parameter_of_rational_sides_and_median ha hc hM

lemma rational_base_den_ne (q : ℚ) : MedianFamily.b q≠0 := by
  intro h
  unfold MedianFamily.b at h
  have hs : ((3*q^2+5)/2)^2=13 := by nlinarith only [h]
  have hn : ¬IsSquare (13 : ℚ) := by norm_num
  exact hn ⟨(3*q^2+5)/2,by nlinarith only [hs]⟩

lemma real_polynomials_at_rational (q : ℚ) :
    realA (q : ℝ)=(MedianFamily.a q : ℝ) ∧
    realB (q : ℝ)=(MedianFamily.b q : ℝ) ∧
    realC (q : ℝ)=(MedianFamily.c q : ℝ) ∧
    realMedianU (q : ℝ)=(MedianFamily.u q : ℝ) := by
  simp only [realA,realB,realC,realMedianU,MedianFamily.a,MedianFamily.b,
    MedianFamily.c,MedianFamily.u]
  push_cast
  exact ⟨by ring,by ring,by ring,by ring⟩

/-- An exact equivalence for the real family. No reciprocal data, range bound,
positive-area condition, or extra-square condition is assumed. -/
theorem rational_parameter_iff_normalized_lengths (r : ℝ) :
    r∈Set.range ((↑) : ℚ → ℝ) ↔ ∃ A C M : ℚ,
      (realA r)^2=(A : ℝ)^2*(realB r)^2 ∧
      (realC r)^2=(C : ℝ)^2*(realB r)^2 ∧
      (realMedianU r)^2=(M : ℝ)^2*(realB r)^2 := by
  constructor
  · rintro ⟨q,rfl⟩
    refine ⟨MedianFamily.a q/MedianFamily.b q,MedianFamily.c q/MedianFamily.b q,
      MedianFamily.u q/MedianFamily.b q,?_⟩
    obtain ⟨ha,hb,hc,hm⟩ := real_polynomials_at_rational q
    rw [ha,hb,hc,hm]
    push_cast
    have hd : (MedianFamily.b q : ℝ)≠0 := by exact_mod_cast rational_base_den_ne q
    constructor
    · field_simp
    constructor <;> field_simp
  · rintro ⟨A,C,M,hA,hC,hM⟩
    exact rational_parameter_of_rational_lengths hA hC hM

#print axioms rational_parameter_iff_normalized_lengths
#print axioms rational_parameter_of_rational_lengths
#print axioms shape_inverse_identity
#print axioms inverse_den_factorization
#print axioms real_side_fibers
#print axioms rational_parameter_or_equilateral
#print axioms rational_parameter_of_rational_sides_and_median
end
end Erdos213.MedianShapeInverse
