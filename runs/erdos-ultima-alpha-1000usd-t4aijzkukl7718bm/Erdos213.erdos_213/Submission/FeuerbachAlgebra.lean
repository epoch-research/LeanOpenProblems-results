import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! Signed-coordinate Feuerbach identities. These construct rational-distance
neighbors of a nine-point center, but do not assert an arbitrary-size clique. -/
namespace Erdos213.FeuerbachAlgebra

lemma feuerbach_polynomial {K : Type*} [CommRing K] (a b c x y : K)
    (ha : a^2=(x-c)^2+y^2) (hb : b^2=x^2+y^2) :
    (y*((c+2*x)*(a+b+c)-4*c*(b+x)))^2 +
      ((y^2+c*x-x^2)*(a+b+c)-4*c*y^2)^2 =
      (a*b*(a+b+c)-4*c*y^2)^2 := by
  let M1 := -(a^2*x^2+a^2*y^2+2*a*b*x^2+2*a*b*y^2+
    2*a*c*x^2+2*a*c*y^2+2*b*c*x^2-6*b*c*y^2+
    c^2*x^2+c^2*y^2-8*c*x*y^2+x^4+2*x^2*y^2+y^4)
  let M2 := -a^4-2*a^3*b-2*a^3*c-a^2*b^2-2*a^2*b*c-a^2*c^2-
    a^2*x^2-a^2*y^2+8*a*c*y^2+c^2*x^2+9*c^2*y^2-
    2*c*x^3-10*c*x*y^2+x^4+2*x^2*y^2+y^4
  linear_combination M1*ha+M2*hb

/-- The nine-point center of the triangle (0,0), (c,0), (x,y). -/
def ninePoint (c x y : ℚ) : ℚ × ℚ :=
  ((c+2*x)/4, (y^2+c*x-x^2)/(4*y))

/-- Signed side lengths give the incenter or one of the excenters. -/
def signedCenter (a b c x y : ℚ) : ℚ × ℚ :=
  (c*(b+x)/(a+b+c), c*y/(a+b+c))

def normBetween (P Q : ℚ × ℚ) : ℚ := (P.1-Q.1)^2+(P.2-Q.2)^2

lemma feuerbach_distance_square (a b c x y : ℚ)
    (hy : y ≠ 0) (hs : a+b+c ≠ 0)
    (ha : a^2=(x-c)^2+y^2) (hb : b^2=x^2+y^2) :
    normBetween (ninePoint c x y) (signedCenter a b c x y) =
      (a*b/(4*y)-c*y/(a+b+c))^2 := by
  have h := feuerbach_polynomial a b c x y ha hb
  unfold normBetween ninePoint signedCenter
  dsimp
  field_simp
  linear_combination h

lemma feuerbach_isSquare (a b c x y : ℚ)
    (hy : y ≠ 0) (hs : a+b+c ≠ 0)
    (ha : a^2=(x-c)^2+y^2) (hb : b^2=x^2+y^2) :
    IsSquare (normBetween (ninePoint c x y) (signedCenter a b c x y)) := by
  refine ⟨a*b/(4*y)-c*y/(a+b+c), ?_⟩
  simpa only [pow_two] using feuerbach_distance_square a b c x y hy hs ha hb

/-- All four sign choices are covered by the same identity. -/
lemma four_signed_neighbors (a b c x y : ℚ)
    (hy : y ≠ 0) (ha : a^2=(x-c)^2+y^2) (hb : b^2=x^2+y^2)
    (e f : ℚ) (he : e^2=1) (hf : f^2=1) (hs : e*a+f*b+c ≠ 0) :
    IsSquare (normBetween (ninePoint c x y) (signedCenter (e*a) (f*b) c x y)) := by
  apply feuerbach_isSquare _ _ _ _ _ hy hs
  · simpa only [mul_pow, he, one_mul] using ha
  · simpa only [mul_pow, hf, one_mul] using hb

#print axioms feuerbach_polynomial
#print axioms feuerbach_distance_square
#print axioms four_signed_neighbors
end Erdos213.FeuerbachAlgebra
