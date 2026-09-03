import Submission.OffsetCircle

/-! The source circle with radius squared twice the center squared, which is
not covered by rational unit-radius normalization, maps to a hyperbola. -/
namespace Erdos213.OffsetCircle.Exceptional

def squarePoint (D x y : ℚ) : ℚ × ℚ := (x^2-D*y^2,2*x*y)
def hyperbolaPoint (x y : ℚ) : ℚ × ℚ := ((x+1)/(2*x),y/(2*x))
def mobius (D : ℚ) (q : ℚ × ℚ) : ℚ × ℚ :=
  ((normSq D q-1)/normSq D (q+(1,0)),2*q.2/normSq D (q+(1,0)))

lemma source_circle_identities (D x y : ℚ) (hc : (x-1)^2+D*y^2=2) :
    normSq D (squarePoint D x y)=(2*x+1)^2 ∧
    normSq D (squarePoint D x y+(1,0))=8*x^2 ∧
    normSq D (squarePoint D x y-(1,0))=8*x+4 := by
  dsimp [normSq,squarePoint]
  constructor
  · linear_combination (x^2+D*y^2+2*x+1)*hc
  constructor
  · linear_combination (x^2+D*y^2+2*x-1)*hc
  · linear_combination (x^2+D*y^2+2*x+3)*hc

lemma mobius_image (D x y : ℚ) (hx : x ≠ 0) (hc : (x-1)^2+D*y^2=2) :
    mobius D (squarePoint D x y)=hyperbolaPoint x y := by
  have hs := source_circle_identities D x y hc
  dsimp [mobius]
  rw [hs.1,hs.2.1]
  apply Prod.ext <;> dsimp [squarePoint,hyperbolaPoint] <;> field_simp <;> ring

lemma image_on_hyperbola (D x y : ℚ) (hx : x ≠ 0) (hc : (x-1)^2+D*y^2=2) :
    (hyperbolaPoint x y).1^2-D*(hyperbolaPoint x y).2^2=1/2 := by
  dsimp [hyperbolaPoint]
  field_simp
  linear_combination -hc

lemma mobius_distance_identity (D : ℚ) (p q : ℚ × ℚ)
    (hp : normSq D (p+(1,0)) ≠ 0) (hq : normSq D (q+(1,0)) ≠ 0) :
    distSq D (mobius D p) (mobius D q)=
      4*distSq D p q/(normSq D (p+(1,0))*normSq D (q+(1,0))) := by
  dsimp [mobius,distSq,normSq] at *
  field_simp
  ring

lemma exceptional_distance_factor (D x y u v : ℚ) (hx : x ≠ 0) (hu : u ≠ 0)
    (hp : (x-1)^2+D*y^2=2) (hq : (u-1)^2+D*v^2=2) :
    distSq D (hyperbolaPoint x y) (hyperbolaPoint u v)=
      distSq D (squarePoint D x y) (squarePoint D u v)/(4*x*u)^2 := by
  rw [← mobius_image D x y hx hp,← mobius_image D u v hu hq]
  have hpx := (source_circle_identities D x y hp).2.1
  have hqu := (source_circle_identities D u v hq).2.1
  rw [mobius_distance_identity D _ _
    (by rw [hpx]; exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hx))
    (by rw [hqu]; exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hu)),hpx,hqu]
  field_simp
  ring

#print axioms source_circle_identities
#print axioms mobius_image
#print axioms image_on_hyperbola
#print axioms exceptional_distance_factor
end Erdos213.OffsetCircle.Exceptional
