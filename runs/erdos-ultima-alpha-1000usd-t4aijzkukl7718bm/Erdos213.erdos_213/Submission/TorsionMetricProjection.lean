import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Euclidean.Sphere.Basic

/-! An exact four-direction metric construction. It does not supply the
remaining direction conditions needed for an eight-point distance set. -/
namespace Erdos213.TorsionMetricProjection

section Algebra
variable {R : Type*} [CommRing R]

def L (t r s : R) : R :=
  (s-r)*t^4+(4*r*s-2*r-2*s)*t^2+s-r

def B (t r s : R) : R :=
  (-2*r^2*s+2*r*s^2+r^2-s^2-r+s)*t^2+r^2+s^2-r-s

def C (t r s : R) : R :=
  (-r^2+s^2)*t^4+(2*r^2*s+2*r*s^2-r^2-s^2-r-s)*t^2-r+s

def J (t r s : R) : R := (s-r)*t^2+r+s-2

def W (t r s : R) : R := t*B t r s
def Z (t r s : R) : R := -C t r s
def V (t r s : R) : R := 4*r*s*t*J t r s*L t r s

lemma projection_square (w z v a m u : R)
    (hu : 2*u*m*w+2*u*z+u^2=v*(m-a)) :
    (w*m+z)^2+v*(m-a)=(w*m+z+u)^2 := by
  linear_combination -hu

lemma negative_t_relation (t r s : R) :
    (-t*W t r s+Z t r s+2*L t r s)^2 =
      (-t*W t r s+Z t r s)^2-2*t*V t r s := by
  unfold W Z V L B C J
  ring

lemma inverse_t_relation (t r s : R) :
    (B t r s+Z t r s+2*r*L t r s)^2 =
      (B t r s+Z t r s)^2+4*r*s*J t r s*L t r s*(1-t^2) := by
  unfold Z L B C J
  ring

lemma negative_inverse_t_relation (t r s : R) :
    (-B t r s+Z t r s+2*s*L t r s)^2 =
      (-B t r s+Z t r s)^2-4*r*s*J t r s*L t r s*(1+t^2) := by
  unfold Z L B C J
  ring
end Algebra

section Rational

def metricA (t r s : ℚ) : ℚ := (Z t r s^2-V t r s*t)/W t r s^2
def metricH (t r s : ℚ) : ℚ := (2*W t r s*Z t r s+V t r s)/(2*W t r s^2)

def rootPlus (t r s : ℚ) : ℚ := (t*W t r s+Z t r s)/W t r s
def rootMinus (t r s : ℚ) : ℚ := (-t*W t r s+Z t r s+2*L t r s)/W t r s
def rootInv (t r s : ℚ) : ℚ := (B t r s+Z t r s+2*r*L t r s)/W t r s
def rootNegInv (t r s : ℚ) : ℚ := (-B t r s+Z t r s+2*s*L t r s)/W t r s

lemma metric_identity (t r s m : ℚ) (hw : W t r s ≠ 0) :
    W t r s^2*(metricA t r s+2*metricH t r s*m+m^2)=
      (W t r s*m+Z t r s)^2+V t r s*(m-t) := by
  unfold metricA metricH
  field_simp
  <;> ring

private lemma metric_square_of_num (t r s m q : ℚ) (hw : W t r s ≠ 0)
    (he : (W t r s*m+Z t r s)^2+V t r s*(m-t)=q^2) :
    metricA t r s+2*metricH t r s*m+m^2=(q/W t r s)^2 := by
  apply (mul_left_cancel₀ (pow_ne_zero 2 hw))
  rw [metric_identity t r s m hw,he]
  field_simp

lemma four_metric_squares (t r s : ℚ) (ht : t ≠ 0) (hw : W t r s ≠ 0) :
    metricA t r s+2*metricH t r s*t+t^2 = rootPlus t r s^2 ∧
    metricA t r s-2*metricH t r s*t+t^2 = rootMinus t r s^2 ∧
    metricA t r s+2*metricH t r s/t+1/t^2 = rootInv t r s^2 ∧
    metricA t r s-2*metricH t r s/t+1/t^2 = rootNegInv t r s^2 := by
  refine ⟨?_,?_,?_,?_⟩
  · exact metric_square_of_num t r s t (t*W t r s+Z t r s) hw (by ring)
  · have he := metric_square_of_num t r s (-t)
      (-t*W t r s+Z t r s+2*L t r s) hw (by
        rw [negative_t_relation]
        ring)
    convert he using 1 <;> ring
  · have he := metric_square_of_num t r s (1/t)
      (B t r s+Z t r s+2*r*L t r s) hw (by
        rw [inverse_t_relation]
        dsimp only [W,V]
        field_simp
        <;> ring)
    convert he using 1 <;> ring
  · have he := metric_square_of_num t r s (-1/t)
      (-B t r s+Z t r s+2*s*L t r s) hw (by
        rw [negative_inverse_t_relation]
        dsimp only [W,V]
        field_simp
        <;> ring)
    convert he using 1 <;> ring

lemma positive_control :
    metricA 2 2 3 = 2589/1280 ∧ metricH 2 2 3 = -957/800 ∧
    metricA 2 2 3-metricH 2 2 3^2 = 378651/640000 ∧
    0 < metricA 2 2 3-metricH 2 2 3^2 := by
  norm_num [metricA,metricH,W,Z,V,L,B,C,J]

lemma positive_control_roots :
    rootPlus 2 2 3 = -89/80 ∧ rootMinus 2 2 3 = -263/80 ∧
    rootInv 2 2 3 = 83/80 ∧ rootNegInv 2 2 3 = 149/80 := by
  norm_num [rootPlus,rootMinus,rootInv,rootNegInv,W,Z,L,B,C]
end Rational

#print axioms projection_square
#print axioms four_metric_squares
#print axioms positive_control
#print axioms positive_control_roots
end Erdos213.TorsionMetricProjection
