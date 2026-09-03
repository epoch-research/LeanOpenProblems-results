import Submission.ProductNormMatching

/-! A necessary elliptic equation for crossed matching in a zero-sum central
source. This is a restricted reduction, not an assertion about all integral
point sets. In particular, no rational-point classification is assumed. -/
namespace Erdos213.ProductCrossZeroSum
open ProductNormMatching
set_option maxHeartbeats 4000000

/-- The two squared radii for b=x+y√(-D) and c=-1-b. -/
def u (D x y : ℚ) : ℚ := radius D x y + radius D (-1-x) (-y)
def v (D x y : ℚ) : ℚ := radius D x y * radius D (-1-x) (-y)

def productMinus (D x y : ℚ) : ℚ :=
  radius D (x*(-1-x)-D*y*(-y)-1) (x*(-y)+y*(-1-x))
def productPlus (D x y : ℚ) : ℚ :=
  radius D (x*(-1-x)-D*y*(-y)+1) (x*(-y)+y*(-1-x))

/-- The crossed pairing, rather than the same-sign pairing. The factor q
is allowed to be arbitrary rational; its squarehood is not needed below. -/
def Crossed (D x y q : ℚ) : Prop :=
  productMinus D x y = q * radius D (x+(-1-x)) (y+(-y)) ∧
  productPlus D x y = q * radius D (x-(-1-x)) (y-(-y))

lemma norm_identities (D x y : ℚ) :
    productMinus D x y = u D x y ^ 2 - 3*v D x y - u D x y + 1 ∧
    productPlus D x y = -(u D x y ^ 2) + 5*v D x y + u D x y + 1 ∧
    radius D (x+(-1-x)) (y+(-y)) = 1 ∧
    radius D (x-(-1-x)) (y-(-y)) = 2*u D x y - 1 := by
  dsimp [productMinus, productPlus, u, v, radius]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

lemma crossed_iff (D x y q : ℚ) : Crossed D x y q ↔
    (u D x y ^ 2 - 3*v D x y - u D x y + 1 = q ∧
     -(u D x y ^ 2) + 5*v D x y + u D x y + 1 = q*(2*u D x y-1)) := by
  obtain ⟨h1,h2,h3,h4⟩ := norm_identities D x y
  simp only [Crossed, h1, h2, h3, h4, mul_one]

lemma radius_relation {D x y q : ℚ} (h : Crossed D x y q) :
    (3*u D x y+1)*v D x y = (u D x y-1)*(u D x y^2+1) := by
  obtain ⟨h1,h2⟩ := (crossed_iff D x y q).mp h
  linear_combination (h2-(2*u D x y-1)*h1)/2

lemma factor_relation {D x y q : ℚ} (h : Crossed D x y q) :
    (3*u D x y+1)*q = u D x y^2-u D x y+4 := by
  obtain ⟨h1,h2⟩ := (crossed_iff D x y q).mp h
  linear_combination -(5*h1+3*h2)/2

lemma radii_positive {D x y : ℚ} (hD : 0 < D) (hy : y ≠ 0) :
    0 < radius D x y ∧ 0 < radius D (-1-x) (-y) := by
  have ht : 0 < D*y^2 := mul_pos hD (sq_pos_of_ne_zero hy)
  dsimp [radius]
  constructor <;> nlinarith [sq_nonneg x, sq_nonneg (-1-x)]

lemma sum_gt_one {D x y q : ℚ} (hD : 0 < D) (hy : y ≠ 0)
    (h : Crossed D x y q) : 1 < u D x y := by
  obtain ⟨hr,hs⟩ := radii_positive hD hy
  have hu : 0 < u D x y := add_pos hr hs
  have hv : 0 < v D x y := mul_pos hr hs
  have hh := radius_relation h
  have hz : 0 < (3*u D x y+1)*v D x y := mul_pos (by linarith) hv
  have hp : 0 < u D x y^2+1 := by positivity
  rw [hh] at hz
  have hpos : 0 < u D x y-1 := (mul_pos_iff_of_pos_right hp).mp hz
  linarith

/-- The elliptic equation used by the reduction. This definition carries no
claim about its rational points. -/
def EllipticEquation (X Y : ℚ) : Prop := Y^2 = X^3-4*X^2+20*X

def ellipticX (U : ℚ) : ℚ := 10*(U-1)/(3*U+1)
def ellipticY (U P : ℚ) : ℚ := 40*P/(3*U+1)

lemma quotient_to_elliptic {U P : ℚ} (hd : 3*U+1 ≠ 0)
    (h : (3*U+1)*P^2=(U-1)*(U^2+1)) :
    EllipticEquation (ellipticX U) (ellipticY U P) := by
  dsimp [EllipticEquation, ellipticX, ellipticY]
  field_simp
  linear_combination 1600*h

lemma ellipticX_ne_zero {U : ℚ} (h : 1 < U) : ellipticX U ≠ 0 := by
  dsimp [ellipticX]
  exact div_ne_zero (mul_ne_zero (by norm_num) (by linarith)) (by linarith)

/-- Every nonreal crossed zero-sum source with rational lengths from the
origin would yield a nonzero rational point on the displayed elliptic curve.
No conclusion about arbitrary configurations is drawn. -/
theorem crossed_produces_nonzero_elliptic_point {D x y q : ℚ}
    (hD : 0 < D) (hy : y ≠ 0)
    (hr : IsSquare (radius D x y))
    (hs : IsSquare (radius D (-1-x) (-y)))
    (h : Crossed D x y q) :
    ∃ X Y : ℚ, X ≠ 0 ∧ EllipticEquation X Y := by
  obtain ⟨R,hR⟩ := hr
  obtain ⟨S,hS⟩ := hs
  rw [← pow_two] at hR hS
  have he : v D x y = (R*S)^2 := by
    dsimp [v]
    rw [hR,hS]
    ring
  have hu := sum_gt_one hD hy h
  refine ⟨ellipticX (u D x y), ellipticY (u D x y) (R*S),
    ellipticX_ne_zero hu, ?_⟩
  apply quotient_to_elliptic (by linarith)
  rw [← he]
  exact radius_relation h

/-- A positive control for the algebra only: its second radius is 2, not a
rational square, so it is not a rational-distance source. -/
theorem matching_control :
    Crossed 1 0 1 1 ∧ radius 1 0 1 = 1 ∧ radius 1 (-1-0) (-1) = 2 := by
  norm_num [Crossed, productMinus, productPlus, radius]

#print axioms norm_identities
#print axioms radius_relation
#print axioms factor_relation
#print axioms sum_gt_one
#print axioms quotient_to_elliptic
#print axioms crossed_produces_nonzero_elliptic_point
#print axioms matching_control
end Erdos213.ProductCrossZeroSum
