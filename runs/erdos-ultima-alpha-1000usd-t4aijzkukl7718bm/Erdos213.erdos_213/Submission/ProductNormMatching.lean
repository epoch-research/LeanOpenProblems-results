import FormalConjecturesUtil

/-! A restriction on one proportional matching of distances in the product
octad {±1,±b,±c,±bc}. This does not bound arbitrary integral point sets. -/
namespace Erdos213.ProductNormMatching
set_option maxHeartbeats 4000000

def radius (D x y : ℚ) : ℚ := x^2+D*y^2
def minusNorm (D x y : ℚ) : ℚ := (x-1)^2+D*y^2
def plusNorm (D x y : ℚ) : ℚ := (x+1)^2+D*y^2
def jRe (D x y : ℚ) : ℚ := x*(radius D x y-1)
def jIm (D x y : ℚ) : ℚ := y*(radius D x y+1)

def SquareInput (D x y : ℚ) : Prop :=
  IsSquare (radius D x y) ∧ IsSquare (minusNorm D x y) ∧ IsSquare (plusNorm D x y)

lemma joukovski_norm (D x y : ℚ) :
    (jRe D x y)^2+D*(jIm D x y)^2 =
      radius D x y*minusNorm D x y*plusNorm D x y := by
  dsimp [jRe,jIm,radius,minusNorm,plusNorm]
  ring

lemma joukovski_square {D x y : ℚ} (h : SquareInput D x y) :
    IsSquare ((jRe D x y)^2+D*(jIm D x y)^2) := by
  rw [joukovski_norm]
  exact (h.1.mul h.2.1).mul h.2.2

/-- Two nonzero perpendicular vectors with rational lengths force the
characteristic of this rational coordinate chart to be a rational square. -/
theorem orthogonal_square_characteristic {D a b c d : ℚ}
    (h1 : IsSquare (a^2+D*b^2)) (h2 : IsSquare (c^2+D*d^2))
    (hn1 : a^2+D*b^2 ≠ 0) (hn2 : c^2+D*d^2 ≠ 0)
    (ho : a*c+D*b*d = 0) : IsSquare D := by
  obtain ⟨u,hu⟩ := h1
  obtain ⟨v,hv⟩ := h2
  rw [← pow_two] at hu hv
  have hu0 : u ≠ 0 := by intro h; apply hn1; simpa [h] using hu
  have hv0 : v ≠ 0 := by intro h; apply hn2; simpa [h] using hv
  have he : D*(a*d-b*c)^2 = (u*v)^2 := by
    linear_combination (c^2+D*d^2)*hu+u^2*hv-(a*c+D*b*d)*ho
  have hd : a*d-b*c ≠ 0 := by
    intro h
    rw [h,zero_pow (by decide : (2 : ℕ) ≠ 0),mul_zero] at he
    exact pow_ne_zero 2 (mul_ne_zero hu0 hv0) he.symm
  refine ⟨u*v/(a*d-b*c), ?_⟩
  field_simp
  linear_combination he

/-- The matching pairs equal signs:
|bc-1|²=q|b-c|² and |bc+1|²=q|b+c|².
The factor q is arbitrary rational here; squarehood of q is not needed. -/
def Matching (D x y z w q : ℚ) : Prop :=
  radius D x y*radius D z w+1-2*(x*z-D*y*w) =
    q*(radius D x y+radius D z w-2*(x*z+D*y*w)) ∧
  radius D x y*radius D z w+1+2*(x*z-D*y*w) =
    q*(radius D x y+radius D z w+2*(x*z+D*y*w))

lemma matching_radius {D x y z w q : ℚ} (h : Matching D x y z w q) :
    radius D x y*radius D z w+1=q*(radius D x y+radius D z w) := by
  linear_combination (h.1+h.2)/2

lemma matching_orthogonal {D x y z w q : ℚ} (h : Matching D x y z w q) :
    jRe D x y*jRe D z w+D*jIm D x y*jIm D z w = 0 := by
  have hr := matching_radius h
  have hh : x*z-D*y*w=q*(x*z+D*y*w) := by
    linear_combination (h.2-h.1)/4
  dsimp [jRe,jIm]
  linear_combination (x*z+D*y*w)*hr-(radius D x y+radius D z w)*hh

/-- This matching cannot provide an extension in a nonsquare characteristic
when the two three-anchor inputs have nonzero radii and anchor distances. -/
theorem matching_forces_square_characteristic {D x y z w q : ℚ}
    (hb : SquareInput D x y) (hc : SquareInput D z w)
    (hb0 : radius D x y*minusNorm D x y*plusNorm D x y ≠ 0)
    (hc0 : radius D z w*minusNorm D z w*plusNorm D z w ≠ 0)
    (hm : Matching D x y z w q) : IsSquare D := by
  apply orthogonal_square_characteristic (joukovski_square hb) (joukovski_square hc)
  · simpa only [joukovski_norm] using hb0
  · simpa only [joukovski_norm] using hc0
  · exact matching_orthogonal hm

/-- The necessary radius equation for a rational proportionality factor.
This statement is not sufficient for any of the anchor or mutual distances. -/
theorem matching_radius_equation {D x y z w R S L : ℚ}
    (hR : radius D x y = R^2) (hS : radius D z w = S^2)
    (hm : Matching D x y z w (L^2)) :
    (R^2+S^2)*L^2=R^2*S^2+1 := by
  have h := matching_radius hm
  rw [hR,hS] at h
  linear_combination -h

/-- Elliptic necessary equation for the radius-only condition. It does not
supply a coordinate lift or any missing square conditions. -/
lemma radius_to_elliptic {R S L : ℚ}
    (h : (R^2+S^2)*L^2=R^2*S^2+1) :
    (R^2*S*(R^2+S^2)*L)^2 =
      (R^2*S^2)*(R^2*S^2+1)*(R^2*S^2+R^4) := by
  linear_combination R^4*S^2*(R^2+S^2)*h

/-- Direct bridges to the squared norm of the product and differences. -/
theorem coordinate_norm_identities (D x y z w : ℚ) :
    (x*z-D*y*w-1)^2+D*(x*w+y*z)^2 =
      radius D x y*radius D z w+1-2*(x*z-D*y*w) ∧
    (x*z-D*y*w+1)^2+D*(x*w+y*z)^2 =
      radius D x y*radius D z w+1+2*(x*z-D*y*w) ∧
    (x-z)^2+D*(y-w)^2 =
      radius D x y+radius D z w-2*(x*z+D*y*w) ∧
    (x+z)^2+D*(y+w)^2 =
      radius D x y+radius D z w+2*(x*z+D*y*w) := by
  dsimp [radius]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- A necessary-equation control, not a point configuration. -/
theorem radius_equation_control :
    (((5/2 : ℚ)^2+(24/11)^2)*(122/73)^2=(5/2)^2*(24/11)^2+1) ∧
    ((5/2 : ℚ)*(24/11)*((5/2)^2-1)*((24/11)^2-1)*
      ((5/2)^2-(24/11)^2) ≠ 0) := by
  norm_num

#print axioms orthogonal_square_characteristic
#print axioms joukovski_square
#print axioms matching_forces_square_characteristic
#print axioms matching_radius_equation
#print axioms radius_to_elliptic
#print axioms coordinate_norm_identities
#print axioms radius_equation_control
end Erdos213.ProductNormMatching
