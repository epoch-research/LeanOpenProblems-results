import FormalConjecturesUtil
import Submission.ProductCayley

/-! A rational elliptic-point construction of all-distance product octads on
two axes. These source octads are degenerate, not witnesses for Erdős 213. -/
namespace Erdos213.ProductAxis
open ReciprocalStar ProductCayley
set_option maxHeartbeats 3000000

def AxisInput (R S : ℚ) : Prop :=
  IsSquare (1+S^2) ∧ IsSquare (R^2+S^2) ∧ IsSquare (1+(R*S)^2)

def axisRatio (S X Y : ℚ) : ℚ := (X^2-S^4)/(2*S*Y)

/-- The two algebraic doubling identities require only the displayed curve
 equation. No rank, torsion, or completeness theorem is a premise. -/
lemma doubling_identities {S X Y : ℚ} (h : Y^2=X*(X+1)*(X+S^4)) :
    (X^2-S^4)^2+4*Y^2=(X^2+2*X+S^4)^2 ∧
    (X^2-S^4)^2+4*S^4*Y^2=(X^2+2*S^4*X+S^4)^2 := by
  constructor
  · linear_combination 4*h
  · linear_combination 4*S^4*h

/-- An elliptic rational point supplies the three required square conditions
for a cross-axis product source. It does not put that source in GP. -/
theorem axisInput_of_curve {S X Y : ℚ} (hS : S ≠ 0) (hY : Y ≠ 0)
    (h0 : IsSquare (1+S^2)) (h : Y^2=X*(X+1)*(X+S^4)) :
    AxisInput (axisRatio S X Y) S := by
  obtain ⟨h1,h2⟩ := doubling_identities h
  have hr : axisRatio S X Y*S=(X^2-S^4)/(2*Y) := by
    dsimp [axisRatio]
    field_simp
  refine ⟨h0,⟨(X^2+2*S^4*X+S^4)/(2*S*Y),?_⟩,
    ⟨(X^2+2*X+S^4)/(2*Y),?_⟩⟩
  · dsimp [axisRatio]
    field_simp
    linear_combination h2
  · rw [hr]
    field_simp
    linear_combination h1

lemma rationalNorm_coordinates {x y : ℚ} (h : IsSquare (x^2+y^2)) :
    RationalNorm ((x : ℂ)+(y : ℂ)*Complex.I) := by
  obtain ⟨r,hr⟩ := h
  rw [← pow_two] at hr
  have hn : Complex.normSq ((x : ℂ)+(y : ℂ)*Complex.I) =
      ((x^2+y^2 : ℚ) : ℝ) := by
    simp [Complex.normSq_apply,pow_two]
  have hr' : ((x^2+y^2 : ℚ) : ℝ) = (r : ℝ)^2 := by exact_mod_cast hr
  refine ⟨|r|,?_⟩
  rw [Complex.norm_def,hn,hr',Real.sqrt_sq_eq_abs]
  norm_cast

lemma rationalNorm_real (x : ℚ) : RationalNorm (x : ℂ) := by
  simpa using rationalNorm_coordinates (x := x) (y := 0) (by simpa using IsSquare.sq x)

lemma rationalNorm_imag (y : ℚ) : RationalNorm ((y : ℂ)*Complex.I) := by
  simpa using rationalNorm_coordinates (x := 0) (y := y) (by simpa using IsSquare.sq y)

lemma imag_compatible_one {S : ℚ} (h : IsSquare (1+S^2)) :
    Compatible ((S : ℂ)*Complex.I) 1 := by
  constructor
  · rw [show (S : ℂ)*Complex.I-1=(-1 : ℂ)+(S : ℂ)*Complex.I by ring]
    simpa only [Rat.cast_neg,Rat.cast_one] using
      rationalNorm_coordinates (x := -1) (y := S) (by simpa using h)
  · rw [add_comm]
    simpa only [Rat.cast_one] using
      rationalNorm_coordinates (x := 1) (y := S) (by simpa using h)

/-- The arithmetic conditions provide the actual complex rational-norm inputs
used by the product construction, not merely a necessary elliptic equation. -/
theorem productInput_of_axisInput {R S : ℚ} (h : AxisInput R S) :
    ProductCayley.Input (R : ℂ) ((S : ℂ)*Complex.I) := by
  refine ⟨rationalNorm_real R,rationalNorm_imag S,⟨?_,?_⟩,
    imag_compatible_one h.1,⟨?_,?_⟩,?_⟩
  · simpa using rationalNorm_real (R-1)
  · simpa using rationalNorm_real (R+1)
  · simpa [sub_eq_add_neg] using
      rationalNorm_coordinates (x := R) (y := -S) (by simpa using h.2.1)
  · exact rationalNorm_coordinates h.2.1
  · simpa only [Rat.cast_mul,mul_assoc] using imag_compatible_one h.2.2

/-- A fully checked source condition, independent of the external rank diagnostic. -/
theorem axis_control : AxisInput (99/190) (8/15) := by
  refine ⟨⟨17/15,?_⟩,⟨85/114,?_⟩,⟨493/475,?_⟩⟩ <;> norm_num

lemma curve_control :
    (416024/1265625 : ℚ)^2 =
      (-2888/5625)*(-2888/5625+1)*(-2888/5625+(8/15)^4) ∧
    axisRatio (8/15) (-2888/5625) (416024/1265625)=99/190 := by
  norm_num [axisRatio]

theorem product_control :
    ProductCayley.Input ((99/190 : ℚ) : ℂ) (((8/15 : ℚ) : ℂ)*Complex.I) :=
  productInput_of_axisInput axis_control

#print axioms doubling_identities
#print axioms axisInput_of_curve
#print axioms rationalNorm_coordinates
#print axioms productInput_of_axisInput
#print axioms axis_control
#print axioms curve_control
#print axioms product_control
end Erdos213.ProductAxis
