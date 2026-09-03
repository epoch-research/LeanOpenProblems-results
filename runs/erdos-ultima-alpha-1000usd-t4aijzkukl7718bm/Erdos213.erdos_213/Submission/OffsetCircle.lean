import Mathlib.Tactic

/-! Algebraic certificates for squaring a circle centered off the origin.
These are restricted construction lemmas, not a solution to Erdős 213. -/
namespace Erdos213.OffsetCircle

def normSq (D : ℚ) (p : ℚ × ℚ) : ℚ := p.1^2+D*p.2^2
def source (c D t : ℚ) : ℚ × ℚ :=
  (c+(1-D*t^2)/(1+D*t^2),2*t/(1+D*t^2))
def point (c D t : ℚ) : ℚ × ℚ :=
  let p := source c D t
  (p.1^2-D*p.2^2,2*p.1*p.2)
def distSq (D : ℚ) (p q : ℚ × ℚ) : ℚ := normSq D (p-q)
def kernel (c D t s : ℚ) : ℚ :=
  ((c+1)-(c-1)*D*t*s)^2+c^2*D*(t+s)^2

def end0 (c : ℚ) : ℚ × ℚ := ((c+1)^2,0)
def endInfinity (c : ℚ) : ℚ × ℚ := ((c-1)^2,0)

lemma denominator_ne_zero (D t : ℚ) (hD : 0 < D) : 1+D*t^2 ≠ 0 := by positivity

lemma source_on_circle (c D t : ℚ) (hD : 0 < D) :
    normSq D (source c D t-(c,0))=1 := by
  have ht := denominator_ne_zero D t hD
  dsimp [normSq,source]
  field_simp
  ring

lemma radius_square (c D t : ℚ) : IsSquare (normSq D (point c D t)) := by
  refine ⟨normSq D (source c D t),?_⟩
  dsimp [normSq,point]
  ring

set_option maxHeartbeats 2000000 in
lemma distance_factor (c D t s : ℚ) (hD : 0 < D) :
    distSq D (point c D t) (point c D s)=
      16*D*(t-s)^2*kernel c D t s/((1+D*t^2)^2*(1+D*s^2)^2) := by
  have ht := denominator_ne_zero D t hD
  have hs := denominator_ne_zero D s hD
  dsimp [distSq,normSq,point,source,kernel]
  field_simp
  ring

lemma kernel_quadratic (c D t s : ℚ) : kernel c D t s =
    D*(c^2+(c-1)^2*D*t^2)*s^2+2*D*t*s+(c+1)^2+c^2*D*t^2 := by
  dsimp [kernel]
  ring

lemma kernel_discriminant (c D t : ℚ) :
    (2*D*t)^2-4*(D*(c^2+(c-1)^2*D*t^2))*((c+1)^2+c^2*D*t^2)=
      -4*D*c^2*((c+1)+(c-1)*D*t^2)^2 := by ring

lemma centered_kernel (D t s : ℚ) : kernel 0 D t s=(1+D*t*s)^2 := by
  dsimp [kernel]
  ring

lemma through_origin_kernel (D t s : ℚ) : kernel 1 D t s=4+D*(t+s)^2 := by
  dsimp [kernel]
  ring

lemma through_origin_norm (D t : ℚ) (hD : 0 < D) :
    normSq D (point 1 D t)=16/(1+D*t^2)^2 := by
  have ht := denominator_ne_zero D t hD
  dsimp [normSq,point,source]
  field_simp
  ring

/-- Inversion of the squared through-origin circle is the previously studied parabola. -/
lemma through_origin_inverse (D t : ℚ) (hD : 0 < D) :
    ((point 1 D t).1/normSq D (point 1 D t),
      -(point 1 D t).2/normSq D (point 1 D t))=((1-D*t^2)/4,-t/2) := by
  have ht := denominator_ne_zero D t hD
  rw [through_origin_norm D t hD]
  apply Prod.ext <;> dsimp [point,source] <;> field_simp <;> ring

def det3 (a b c d e f g h i : ℚ) : ℚ :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)
def triangle (a b c : ℚ × ℚ) : ℚ :=
  (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1)
def circle (D : ℚ) (a b c d : ℚ × ℚ) : ℚ :=
  det3 (b.1-a.1) (b.2-a.2) (distSq D a b)
    (c.1-a.1) (c.2-a.2) (distSq D a c)
    (d.1-a.1) (d.2-a.2) (distSq D a d)

set_option maxHeartbeats 2000000 in
lemma endpoint_circle_factor (c D t s : ℚ) (hD : 0 < D) :
    circle D (end0 c) (endInfinity c) (point c D t) (point c D s)=
      256*c*D*t*s*(t-s)*((c+1)-(c-1)*D*t*s)/
        ((1+D*t^2)^2*(1+D*s^2)^2) := by
  have ht := denominator_ne_zero D t hD
  have hs := denominator_ne_zero D s hD
  dsimp [circle,det3,end0,endInfinity,distSq,normSq,point,source]
  field_simp
  ring

lemma partner_kernel (c D t : ℚ) (hc : c ≠ 1) (hD : D ≠ 0) (ht : t ≠ 0) :
    kernel c D t ((c+1)/((c-1)*D*t))=
      c^2*D*(t+(c+1)/((c-1)*D*t))^2 := by
  have hc' : c-1 ≠ 0 := sub_ne_zero.mpr hc
  dsimp [kernel]
  field_simp
  ring

/-- The obvious torsion partner has a zero circle determinant with the two endpoints. -/
lemma partner_circle (c D t : ℚ) (hc : c ≠ 1) (hD : 0 < D) (ht : t ≠ 0) :
    circle D (end0 c) (endInfinity c) (point c D t)
      (point c D ((c+1)/((c-1)*D*t)))=0 := by
  have hc' : c-1 ≠ 0 := sub_ne_zero.mpr hc
  have hD' : D ≠ 0 := ne_of_gt hD
  rw [endpoint_circle_factor c D t _ hD]
  have hz : (c+1)-(c-1)*D*t*((c+1)/((c-1)*D*t))=0 := by field_simp; ring
  rw [hz,mul_zero,zero_div]

lemma anchor_product (c t : ℚ) :
    ((c+1)^2+c^2*t^2)*(c^2+(c-1)^2*t^2)=
      c^2*((c+1)+(c-1)*t^2)^2+t^2 := by ring

def ellipticX (c t : ℚ) : ℚ := c^2*(c-1)^2*t^2
lemma elliptic_anchor_identities (c t : ℚ) :
    ellipticX c t+(c^2-1)^2=(c-1)^2*kernel c 1 0 t ∧
      ellipticX c t+c^4=c^2*(c^2+(c-1)^2*t^2) := by
  dsimp [ellipticX,kernel]
  constructor <;> ring

lemma seed_identities (c h : ℚ) (hc : c ≠ 1) (hh : h^2=c^2+4) :
    kernel c 1 0 (2/(c-1))=((c^2+1)/(c-1))^2 ∧
      c^2+(c-1)^2*(2/(c-1))^2=h^2 := by
  have hc' : c-1 ≠ 0 := sub_ne_zero.mpr hc
  constructor
  · dsimp [kernel]
    field_simp
    ring
  · field_simp
    linear_combination -hh

lemma seed_point (c h : ℚ) (hh : h^2=c^2+4) :
    (2*c^2*(c^2+1)*h)^2=(4*c^2)*((4*c^2)+(c^2-1)^2)*((4*c^2)+c^4) := by
  linear_combination 4*c^4*(c^2+1)^2*hh

lemma four_torsion_equation (c : ℚ) :
    (c^2*(c^2-1)*(2*c^2-1))^2=
      (c^2*(c^2-1))*((c^2*(c^2-1))+(c^2-1)^2)*((c^2*(c^2-1))+c^4) := by ring

def kite : Fin 4 → ℚ × ℚ := ![(880,0),(13,0),(0,84),(0,-84)]
def normalizeControl (p : ℚ × ℚ) : ℚ × ℚ := ((p.1-185/1156)*(289/2),p.2*(289/2))

lemma control_images :
    normalizeControl (end0 (3/2))=kite 0 ∧
    normalizeControl (endInfinity (3/2))=kite 1 ∧
    normalizeControl (point (3/2) 1 4)=kite 2 ∧
    normalizeControl (point (3/2) 1 (-4))=kite 3 := by
  decide +kernel

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 10000 in
lemma kite_certificate : Function.Injective kite ∧
    (∀ i j, IsSquare (distSq 1 (kite i) (kite j))) ∧
    (∀ i j k, i ≠ j → i ≠ k → j ≠ k → triangle (kite i) (kite j) (kite k) ≠ 0) ∧
    circle 1 (kite 0) (kite 1) (kite 2) (kite 3) ≠ 0 := by
  decide +kernel

#print axioms source_on_circle
#print axioms radius_square
#print axioms distance_factor
#print axioms through_origin_inverse
#print axioms endpoint_circle_factor
#print axioms partner_circle
#print axioms seed_identities
#print axioms seed_point
#print axioms four_torsion_equation
#print axioms control_images
#print axioms kite_certificate
end Erdos213.OffsetCircle
