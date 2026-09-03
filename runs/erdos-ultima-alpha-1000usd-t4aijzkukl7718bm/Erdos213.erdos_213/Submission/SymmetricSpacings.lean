import Mathlib.Algebra.Group.Even
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Exact rational constructions for symmetric collinear distance anchors.
These lemmas do not assert a cardinality increase in general position. -/
namespace Erdos213.SymmetricSpacings

section Field
variable {K : Type*} [Field K]

def quartic (c₀ c₁ c₂ c₃ c₄ t : K) : K :=
  c₀ + c₁*t + c₂*t^2 + c₃*t^3 + c₄*t^4

def quadratic (c₀ c₁ c₂ t : K) : K := c₀+c₁*t+c₂*t^2

lemma quartic_interpolation (c₀ c₁ c₂ c₃ c₄ t u v w : K)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    quartic c₀ c₁ c₂ c₃ c₄ t =
      quartic c₀ c₁ c₂ c₃ c₄ u * (t-v)*(t-w)/((u-v)*(u-w)) +
      quartic c₀ c₁ c₂ c₃ c₄ v * (t-u)*(t-w)/((v-u)*(v-w)) +
      quartic c₀ c₁ c₂ c₃ c₄ w * (t-u)*(t-v)/((w-u)*(w-v)) +
      (t-u)*(t-v)*(t-w)*(c₄*(t+u+v+w)+c₃) := by
  unfold quartic
  field_simp [sub_ne_zero.mpr huv, sub_ne_zero.mpr huw, sub_ne_zero.mpr hvw,
    sub_ne_zero.mpr huv.symm, sub_ne_zero.mpr huw.symm, sub_ne_zero.mpr hvw.symm]
  <;> ring

lemma quartic_fourth_root (c₀ c₁ c₂ c₃ c₄ u v w : K)
    (hc : c₄ ≠ 0) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hu : quartic c₀ c₁ c₂ c₃ c₄ u = 0)
    (hv : quartic c₀ c₁ c₂ c₃ c₄ v = 0)
    (hw : quartic c₀ c₁ c₂ c₃ c₄ w = 0) :
    quartic c₀ c₁ c₂ c₃ c₄ (-c₃/c₄-u-v-w) = 0 := by
  have hlast : c₄*((-c₃/c₄-u-v-w)+u+v+w)+c₃ = 0 := by
    field_simp
    <;> ring
  rw [quartic_interpolation c₀ c₁ c₂ c₃ c₄ _ u v w huv huw hvw,
    hu, hv, hw, hlast]
  simp

lemma quartic_sub_square (c₀ c₁ c₂ c₃ c₄ g₀ g₁ g₂ t : K) :
    quartic c₀ c₁ c₂ c₃ c₄ t - (quadratic g₀ g₁ g₂ t)^2 =
      quartic (c₀-g₀^2) (c₁-2*g₀*g₁) (c₂-g₁^2-2*g₀*g₂)
        (c₃-2*g₁*g₂) (c₄-g₂^2) t := by
  unfold quartic quadratic
  ring

lemma parabola_fourth_square (c₀ c₁ c₂ c₃ c₄ g₀ g₁ g₂ u v w : K)
    (hc : c₄-g₂^2 ≠ 0) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hu : quartic c₀ c₁ c₂ c₃ c₄ u = (quadratic g₀ g₁ g₂ u)^2)
    (hv : quartic c₀ c₁ c₂ c₃ c₄ v = (quadratic g₀ g₁ g₂ v)^2)
    (hw : quartic c₀ c₁ c₂ c₃ c₄ w = (quadratic g₀ g₁ g₂ w)^2) :
    IsSquare (quartic c₀ c₁ c₂ c₃ c₄ (-(c₃-2*g₁*g₂)/(c₄-g₂^2)-u-v-w)) := by
  have hh := quartic_fourth_root (c₀-g₀^2) (c₁-2*g₀*g₁) (c₂-g₁^2-2*g₀*g₂)
    (c₃-2*g₁*g₂) (c₄-g₂^2) u v w hc huv huw hvw
    (by rw [← quartic_sub_square, hu, sub_self])
    (by rw [← quartic_sub_square, hv, sub_self])
    (by rw [← quartic_sub_square, hw, sub_self])
  rw [← quartic_sub_square] at hh
  exact ⟨quadratic g₀ g₁ g₂ _, by simpa only [pow_two] using (sub_eq_zero.mp hh)⟩

end Field

def spacing (x a t : ℚ) : ℚ := 2*(x-a*t)/(t^2-1)

def spacingQuartic (x a t : ℚ) : ℚ :=
  (2*(x-a*t))^2 - 2*x*(2*(x-a*t))*(t^2-1) + a^2*(t^2-1)^2

lemma spacingQuartic_coefficients (x a t : ℚ) :
    spacingQuartic x a t = quartic (8*x^2+a^2) (-12*a*x)
      (2*a^2-4*x^2) (4*a*x) (a^2) t := by
  unfold spacingQuartic quartic
  ring

lemma first_spacing_square (x a t : ℚ) (h : t^2-1 ≠ 0) :
    (a+t*spacing x a t)^2 = (spacing x a t)^2+2*x*spacing x a t+a^2 := by
  unfold spacing
  field_simp
  <;> ring

lemma symmetric_spacing_squares (x a t : ℚ) (h : t^2-1 ≠ 0)
    (hs : IsSquare (spacingQuartic x a t)) :
    IsSquare ((spacing x a t)^2+2*x*spacing x a t+a^2) ∧
    IsSquare ((spacing x a t)^2-2*x*spacing x a t+a^2) := by
  constructor
  · exact ⟨a+t*spacing x a t, by simpa only [pow_two] using (first_spacing_square x a t h).symm⟩
  · obtain ⟨y,hy⟩ := hs
    refine ⟨y/(t^2-1), ?_⟩
    have hy' : y^2 = spacingQuartic x a t := by simpa only [pow_two] using hy.symm
    unfold spacing
    field_simp
    rw [hy']
    unfold spacingQuartic
    ring

lemma reciprocal_spacing_squares (x a r : ℚ) (hr : r ≠ 0)
    (hp : IsSquare (r^2+2*x*r+a^2)) (hm : IsSquare (r^2-2*x*r+a^2)) :
    IsSquare ((a^2/r)^2+2*x*(a^2/r)+a^2) ∧
    IsSquare ((a^2/r)^2-2*x*(a^2/r)+a^2) := by
  obtain ⟨u,hu⟩ := hp
  obtain ⟨v,hv⟩ := hm
  constructor
  · refine ⟨a*u/r, ?_⟩
    field_simp
    have hh := congrArg (fun z : ℚ => a^2*z) hu
    dsimp at hh
    linear_combination hh
  · refine ⟨a*v/r, ?_⟩
    field_simp
    have hh := congrArg (fun z : ℚ => a^2*z) hv
    dsimp at hh
    linear_combination hh


def doubleSpacing (a r y : ℚ) : ℚ := (r^4-a^4)/(2*r*y)

lemma doubling_identity (x a r y : ℚ) :
    ((r^2+a^2)*y+2*x*r*(r^2-a^2))^2 -
      ((r^4-a^4)^2+4*x*r*y*(r^4-a^4)+4*a^2*r^2*y^2) =
    (r^2-a^2)^2*(y^2-((r^2+a^2)^2-4*x^2*r^2)) := by
  ring

lemma double_spacing_plus (x a r y : ℚ) (hr : r ≠ 0) (hy : y ≠ 0)
    (he : y^2 = (r^2+a^2)^2-4*x^2*r^2) :
    IsSquare ((doubleSpacing a r y)^2+2*x*doubleSpacing a r y+a^2) := by
  have hh : ((r^2+a^2)*y+2*x*r*(r^2-a^2))^2 =
      (r^4-a^4)^2+4*x*r*y*(r^4-a^4)+4*a^2*r^2*y^2 := by
    apply sub_eq_zero.mp
    rw [doubling_identity, he, sub_self, mul_zero]
  refine ⟨((r^2+a^2)*y+2*x*r*(r^2-a^2))/(2*r*y), ?_⟩
  unfold doubleSpacing
  field_simp
  linear_combination -hh

lemma double_spacing_squares (x a r y : ℚ) (hr : r ≠ 0) (hy : y ≠ 0)
    (he : y^2 = (r^2+a^2)^2-4*x^2*r^2) :
    IsSquare ((doubleSpacing a r y)^2+2*x*doubleSpacing a r y+a^2) ∧
    IsSquare ((doubleSpacing a r y)^2-2*x*doubleSpacing a r y+a^2) := by
  refine ⟨double_spacing_plus x a r y hr hy he, ?_⟩
  have hh := double_spacing_plus (-x) a r y hr hy
    (by convert he using 1 <;> ring)
  convert hh using 1 <;> ring

#print axioms quartic_fourth_root
#print axioms parabola_fourth_square
#print axioms symmetric_spacing_squares
#print axioms reciprocal_spacing_squares
#print axioms double_spacing_squares
end Erdos213.SymmetricSpacings
