import Submission.PrimitiveQuadratic
import Submission.PolynomialSquareValues

/-! Uniform integer-parameter version of the restricted quadratic-extension
obstruction. No global cardinality assertion is made. -/
namespace Erdos213.PrimitiveQuadraticInteger
open Polynomial CircleLineRigidity PrimitiveQuadratic PrimitiveQuadraticCases
noncomputable section

def rationalNorm (ax ay bx byy cx cy : ℚ) : ℚ[X] :=
  (quad ax bx cx)^2+(quad ay byy cy)^2

def qcomplex (x y : ℚ) : ℂ := (x : ℂ)+(y : ℂ)*Complex.I

lemma norm_real_square (ax ay bx byy cx cy : ℚ)
    (hs : ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      IsSquare ((ax*(n : ℚ)^2+bx*n+cx)^2+(ay*(n : ℚ)^2+byy*n+cy)^2)) :
    IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (normPolynomial (qcomplex ax ay) (qcomplex bx byy) (qcomplex cx cy))) := by
  have h : IsSquare (rationalNorm ax ay bx byy cx cy) := by
    apply PolynomialSquareValues.isSquare_of_eventually_int_eval
    simpa only [rationalNorm,eval_add,eval_pow,quad,eval_mul,eval_C,eval_X] using hs
  have hr := h.map (Polynomial.mapRingHom (Rat.castHom ℝ))
  have he : (rationalNorm ax ay bx byy cx cy).map (Rat.castHom ℝ)=
      normPolynomial (qcomplex ax ay) (qcomplex bx byy) (qcomplex cx cy) := by
    simp [rationalNorm,normPolynomial,qcomplex,Polynomial.map_add,Polynomial.map_pow,quad_map]
  change IsSquare ((rationalNorm ax ay bx byy cx cy).map (Rat.castHom ℝ)) at hr
  rw [he] at hr
  exact hr.map (algebraMap ℝ[X] (RatFunc ℝ))

lemma eventual_norm_type (ax ay bx byy cx cy : ℚ)
    (hs : ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      IsSquare ((ax*(n : ℚ)^2+bx*n+cx)^2+(ay*(n : ℚ)^2+byy*n+cy)^2)) :
    lineType (ax : ℝ) ay bx byy cx cy ∨ nullType (ax : ℝ) ay bx byy cx cy := by
  simpa [qcomplex] using norm_type (qcomplex ax ay) (qcomplex bx byy) (qcomplex cx cy)
    (norm_real_square ax ay bx byy cx cy hs)

/-- A rational quadratic path with rational distances to each of the four fixed
anchors at EVERY sufficiently large integer parameter stays on a coordinate
axis. The threshold may differ between the four distance conditions. -/
theorem integer_extension_axes (ax ay bx byy cx cy : ℚ)
    (h0 : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsSquare
      ((ax*(n : ℚ)^2+(bx+8)*n+cx)^2+(ay*(n : ℚ)^2+byy*n+cy)^2))
    (h1 : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsSquare
      ((ax*(n : ℚ)^2+(bx-8)*n+cx)^2+(ay*(n : ℚ)^2+byy*n+cy)^2))
    (h2 : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsSquare
      ((ax*(n : ℚ)^2+bx*n+cx)^2+((ay-4)*(n : ℚ)^2+byy*n+(cy+4))^2))
    (h3 : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsSquare
      ((ax*(n : ℚ)^2+bx*n+cx)^2+((ay-16)*(n : ℚ)^2+byy*n+(cy+1))^2)) :
    (ax=0 ∧ bx=0 ∧ cx=0) ∨ (ay=0 ∧ byy=0 ∧ cy=0) := by
  have hh : ((ax : ℝ)=0 ∧ (bx : ℝ)=0 ∧ (cx : ℝ)=0) ∨
      ((ay : ℝ)=0 ∧ (byy : ℝ)=0 ∧ (cy : ℝ)=0) := by
    apply extension_types_axes
    · simpa using eventual_norm_type ax ay (bx+8) byy cx cy h0
    · simpa using eventual_norm_type ax ay (bx-8) byy cx cy h1
    · simpa using eventual_norm_type ax (ay-4) bx byy cx (cy+4) h2
    · simpa using eventual_norm_type ax (ay-16) bx byy cx (cy+1) h3
  exact_mod_cast hh

/-- The axis conclusion expressed as ordinary real affine collinearity. -/
theorem integer_extension_collinear (ax ay bx byy cx cy : ℚ)
    (h0 : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsSquare
      ((ax*(n : ℚ)^2+(bx+8)*n+cx)^2+(ay*(n : ℚ)^2+byy*n+cy)^2))
    (h1 : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsSquare
      ((ax*(n : ℚ)^2+(bx-8)*n+cx)^2+(ay*(n : ℚ)^2+byy*n+cy)^2))
    (h2 : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsSquare
      ((ax*(n : ℚ)^2+bx*n+cx)^2+((ay-4)*(n : ℚ)^2+byy*n+(cy+4))^2))
    (h3 : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsSquare
      ((ax*(n : ℚ)^2+bx*n+cx)^2+((ay-16)*(n : ℚ)^2+byy*n+(cy+1))^2)) (t : ℝ) :
    Collinear ℝ ({(4*(t : ℂ)^2-4)*Complex.I,(16*(t : ℂ)^2-1)*Complex.I,
      qcomplex ax ay*(t : ℂ)^2+qcomplex bx byy*t+qcomplex cx cy} : Set ℂ) ∨
    Collinear ℝ ({-8*(t : ℂ),8*(t : ℂ),
      qcomplex ax ay*(t : ℂ)^2+qcomplex bx byy*t+qcomplex cx cy} : Set ℂ) := by
  rcases integer_extension_axes ax ay bx byy cx cy h0 h1 h2 h3 with h | h
  · left
    apply collinear_of_re_zero
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl <;> simp [qcomplex,pow_two,h.1,h.2.1,h.2.2]
  · right
    apply collinear_of_im_zero
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl <;> simp [qcomplex,pow_two,h.1,h.2.1,h.2.2]

#print axioms norm_real_square
#print axioms integer_extension_axes
#print axioms integer_extension_collinear
end
end Erdos213.PrimitiveQuadraticInteger
