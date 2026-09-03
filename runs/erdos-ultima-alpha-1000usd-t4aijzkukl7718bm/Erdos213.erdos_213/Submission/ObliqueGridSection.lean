import Mathlib.Tactic

/-! Five square direction lengths in a genuinely oblique positive metric.
Two further direction conditions are still needed for the eight-point grid
transformation. No eight-point existence or arbitrary-cardinality theorem
is asserted here. -/
namespace Erdos213.ObliqueGridSection
set_option maxHeartbeats 2000000

section Algebra
variable {R : Type*} [CommRing R]

def W (r s : R) : R := 2*r^2*s-2*r*s^2-3*r^2-s^2+3*r+s
def Z (r s : R) : R := 4*r^2*s+4*r*s^2-3*r^2-s^2-6*r+2*s
def V (r s : R) : R := 4*r*s*(r+3*s-4)*(8*r*s-9*r+s)
def L (r s : R) : R := -16*r*s+18*r-2*s

def rootZero (r s : R) : R :=
  3*(r+2)*(s-1)*(s-r)-(r+1)*s*(s-r)-4*(2*r-1)*s*(s-1)

lemma four_numerator_identities (r s : R) :
    (-W r s+Z r s)^2-2*V r s=(-W r s+Z r s+L r s)^2 ∧
    (2*W r s+Z r s)^2+V r s=(2*W r s+Z r s+r*L r s)^2 ∧
    (-2*W r s+Z r s)^2-3*V r s=(-2*W r s+Z r s+s*L r s)^2 := by
  unfold W Z V L
  constructor
  · ring
  constructor <;> ring

lemma secant_identity (r s : R) :
    Z r s^2-V r s-rootZero r s^2=
      -4*(r-1)*s*(s-1)*(s-r)*(5*(r-4)*s+3*(r^2+8)) := by
  unfold Z V rootZero
  ring
end Algebra

section Rational

def metricA (r s : ℚ) : ℚ := (Z r s^2-V r s)/W r s^2
def metricH (r s : ℚ) : ℚ := (2*W r s*Z r s+V r s)/(2*W r s^2)
def directionNorm (r s m : ℚ) : ℚ := metricA r s+2*metricH r s*m+m^2

def sectionParam (r : ℚ) : ℚ := -3*(r^2+8)/(5*(r-4))

lemma metric_identity (r s m : ℚ) (hw : W r s ≠ 0) :
    W r s^2*directionNorm r s m=(W r s*m+Z r s)^2+V r s*(m-1) := by
  unfold directionNorm metricA metricH
  field_simp
  <;> ring

lemma square_of_numerator (r s m q : ℚ) (hw : W r s ≠ 0)
    (he : (W r s*m+Z r s)^2+V r s*(m-1)=q^2) :
    IsSquare (directionNorm r s m) := by
  refine ⟨q/W r s, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 hw)
  rw [metric_identity r s m hw, he]
  field_simp

lemma four_direction_squares (r s : ℚ) (hw : W r s ≠ 0) :
    IsSquare (directionNorm r s 1) ∧ IsSquare (directionNorm r s (-1)) ∧
    IsSquare (directionNorm r s 2) ∧ IsSquare (directionNorm r s (-2)) := by
  have hn := four_numerator_identities r s
  refine ⟨square_of_numerator r s 1 (W r s+Z r s) hw (by ring), ?_, ?_, ?_⟩
  · apply square_of_numerator r s (-1) (-W r s+Z r s+L r s) hw
    convert hn.1 using 1 <;> ring
  · apply square_of_numerator r s 2 (2*W r s+Z r s+r*L r s) hw
    convert hn.2.1 using 1 <;> ring
  · apply square_of_numerator r s (-2) (-2*W r s+Z r s+s*L r s) hw
    convert hn.2.2 using 1 <;> ring

lemma zero_direction_square (r : ℚ) (hr : r ≠ 4)
    (hw : W r (sectionParam r) ≠ 0) :
    IsSquare (directionNorm r (sectionParam r) 0) := by
  apply square_of_numerator r (sectionParam r) 0 (rootZero r (sectionParam r)) hw
  have he : 5*(r-4)*sectionParam r+3*(r^2+8)=0 := by
    unfold sectionParam
    have hr' : r-4 ≠ 0 := sub_ne_zero.mpr hr
    field_simp
    <;> ring
  have hi := secant_identity r (sectionParam r)
  rw [he, mul_zero] at hi
  simpa [sub_eq_add_neg] using (sub_eq_zero.mp hi)

lemma five_directions (r : ℚ) (hr : r ≠ 4) (hw : W r (sectionParam r) ≠ 0) :
    ∀ m ∈ ({-2,-1,0,1,2} : Set ℚ), IsSquare (directionNorm r (sectionParam r) m) := by
  have h := four_direction_squares r (sectionParam r) hw
  intro m hm
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · exact h.2.2.2
  · exact h.2.1
  · exact zero_direction_square r hr hw
  · exact h.1
  · exact h.2.2.1

lemma positive_control :
    sectionParam 2=18/5 ∧ metricA 2 (18/5)=6889/1600 ∧
    metricH 2 (18/5)=23/80 ∧
    metricA 2 (18/5)-metricH 2 (18/5)^2=27027/6400 ∧
    0 < metricA 2 (18/5)-metricH 2 (18/5)^2 := by
  norm_num [sectionParam, metricA, metricH, W, Z, V]

lemma remaining_control :
    directionNorm 2 (18/5) (1/2)=7749/1600 ∧
    directionNorm 2 (18/5) (-1/2)=6829/1600 ∧
    ¬ IsSquare (directionNorm 2 (18/5) (1/2)) ∧
    ¬ IsSquare (directionNorm 2 (18/5) (-1/2)) := by
  decide +kernel
end Rational

#print axioms secant_identity
#print axioms five_directions
#print axioms positive_control
#print axioms remaining_control
end Erdos213.ObliqueGridSection
