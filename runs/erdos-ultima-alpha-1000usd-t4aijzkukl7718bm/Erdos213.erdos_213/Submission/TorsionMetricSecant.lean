import Submission.TorsionMetricProjection

/-! A nonconstant-parameter section of the fifth metric-square condition.
This does not assert the remaining chord conditions of a torsion octet. -/
namespace Erdos213.TorsionMetricSecant
open TorsionMetricProjection
set_option maxHeartbeats 4000000

section Algebra
variable {R : Type*} [CommRing R]

def g (t : R) : R := t^4+4*t^2-1

def fifthNumerator (t r s : R) : R :=
  (g t*B t r s-4*t*C t r s)^2 +
    16*r*s*t*J t r s*L t r s*(g t-4*t^3)

def e0 (t r : R) : R :=
  t^4*r-t^4+4*t^3*r+4*t^2*r-4*t^2+4*t-r+1

def e1 (t r : R) : R := t^3*r-3*t^2*r+4*t^2+t*r+4*t+r

def e2 (t r : R) : R := t^4+8*t^3*r-4*t^3+4*t^2-1

def secantRoot (t r s : R) : R :=
  (t^2+1)*e0 t r*(s-1)*(s-r) -
    (t+1)*(t-1)^2*e1 t r*s*(s-r) - 2*e2 t r*s*(s-1)

def sectionNum (t r : R) : R :=
  (t^2+1)*(t^5*r^2+5*t^4*r^2+8*t^3*r^2+4*t^2*r^2+
    2*t^3-t*r^2+2*t^2-r^2+10*t+2)

def sectionDen (t r : R) : R :=
  (t^2*r-r+2)*(t^5+5*t^4+10*t^3-2*t^2+t+1)

lemma secant_identity (t r s : R) :
    fifthNumerator t r s - secantRoot t r s^2 =
      4*(r-1)*(t-1)^3*(t^2-2*t-1)*s*(s-1)*(s-r)*
        (sectionDen t r*s-sectionNum t r) := by
  unfold fifthNumerator secantRoot sectionDen sectionNum e0 e1 e2 g B C J L
  ring

lemma fifth_square_of_section (t r s : R)
    (h : sectionDen t r*s=sectionNum t r) :
    fifthNumerator t r s=secantRoot t r s^2 := by
  have he := secant_identity t r s
  rw [h, sub_self, mul_zero] at he
  exact sub_eq_zero.mp he
end Algebra

section Rational

def sectionParam (t r : ℚ) : ℚ := sectionNum t r/sectionDen t r

def fifthSlope (t : ℚ) : ℚ := g t/(4*t^2)

lemma section_square (t r : ℚ) (hd : sectionDen t r ≠ 0) :
    fifthNumerator t r (sectionParam t r)=
      secantRoot t r (sectionParam t r)^2 := by
  apply fifth_square_of_section
  simp only [sectionParam]
  field_simp

lemma fifth_metric_identity (t r s : ℚ) (ht : t ≠ 0) (hw : W t r s ≠ 0) :
    (4*t*W t r s)^2*
      (metricA t r s+2*metricH t r s*fifthSlope t+fifthSlope t^2)=
        fifthNumerator t r s := by
  calc
    _ = (4*t)^2 * (W t r s^2*
        (metricA t r s+2*metricH t r s*fifthSlope t+fifthSlope t^2)) := by ring
    _ = (4*t)^2 * ((W t r s*fifthSlope t+Z t r s)^2+
        V t r s*(fifthSlope t-t)) := by rw [metric_identity t r s _ hw]
    _ = _ := by
      unfold fifthSlope fifthNumerator W Z V
      field_simp
      <;> ring

lemma fifth_metric_square (t r : ℚ) (ht : t ≠ 0) (hd : sectionDen t r ≠ 0)
    (hw : W t r (sectionParam t r) ≠ 0) :
    metricA t r (sectionParam t r)+
      2*metricH t r (sectionParam t r)*fifthSlope t+fifthSlope t^2 =
        (secantRoot t r (sectionParam t r)/(4*t*W t r (sectionParam t r)))^2 := by
  have hc : 4*t*W t r (sectionParam t r) ≠ 0 := by exact mul_ne_zero (mul_ne_zero (by norm_num) ht) hw
  apply mul_left_cancel₀ (pow_ne_zero 2 hc)
  rw [fifth_metric_identity t r _ ht hw, section_square t r hd]
  field_simp

lemma section_control : sectionParam 2 2 = 2005/748 := by
  norm_num [sectionParam, sectionNum, sectionDen]

lemma positive_control :
    metricA 2 2 (2005/748) = 2758661199024/916857955729 ∧
    metricH 2 2 (2005/748) = -959941620876/916857955729 ∧
    0 < metricA 2 2 (2005/748)-metricH 2 2 (2005/748)^2 := by
  norm_num [metricA, metricH, W, Z, V, L, B, C, J]

lemma five_control_roots :
    ∀ m ∈ ({2,-2,1/2,-1/2,31/16} : Set ℚ),
      IsSquare (metricA 2 2 (2005/748)+2*metricH 2 2 (2005/748)*m+m^2) := by
  intro m hm
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · refine ⟨1608206/957527, ?_⟩
    norm_num [metricA, metricH, W, Z, V, L, B, C, J]
  · refine ⟨3204038/957527, ?_⟩
    norm_num [metricA, metricH, W, Z, V, L, B, C, J]
  · refine ⟨2848111/1915054, ?_⟩
    norm_num [metricA, metricH, W, Z, V, L, B, C, J]
  · refine ⟨3973823/1915054, ?_⟩
    norm_num [metricA, metricH, W, Z, V, L, B, C, J]
  · refine ⟨25200311/15320432, ?_⟩
    norm_num [metricA, metricH, W, Z, V, L, B, C, J]
end Rational

#print axioms secant_identity
#print axioms fifth_metric_square
#print axioms positive_control
#print axioms five_control_roots
end Erdos213.TorsionMetricSecant
