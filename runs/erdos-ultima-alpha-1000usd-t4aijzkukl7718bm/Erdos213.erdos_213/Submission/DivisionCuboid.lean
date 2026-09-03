import Submission.CommonFaceClass
import Mathlib.Analysis.Complex.Basic

/-! The elementary norm conditions arising in one elliptic-division projection
are a perfect-cuboid condition. Neither existence nor nonexistence of perfect
cuboids, and no settlement of Erdos 213, is asserted. -/
namespace Erdos213.DivisionCuboid
open CommonFaceClass

def radiusSq (x y : ℚ) : ℚ := x^2+y^2

def normZ (x y : ℚ) : ℚ := ((radiusSq x y-1)^2+4*x^2)/(4*radiusSq x y)
def normW (x y : ℚ) : ℚ := ((radiusSq x y-1)^2+4*y^2)/(4*radiusSq x y)

/-- A rational perfect cuboid, with positive edge lengths. Clearing the finitely
many denominators gives the usual integral formulation. -/
def RationalPerfectCuboid : Prop := ∃ a b c : ℚ, 0<a ∧ 0<b ∧ 0<c ∧
  IsSquare (a^2+b^2) ∧ IsSquare (a^2+c^2) ∧ IsSquare (b^2+c^2) ∧
  IsSquare (a^2+b^2+c^2)

lemma sphere_identity (x y : ℚ) :
    (2*x)^2+(2*y)^2+(radiusSq x y-1)^2=(radiusSq x y+1)^2 := by
  dsimp [radiusSq]
  ring

/-- The two face-ratio conditions force the parameter itself to have rational
norm; this is not a consequence of real algebra alone. -/
theorem radius_square_of_norms (x y : ℚ) (hs : 0<radiusSq x y)
    (hz : IsSquare (normZ x y)) (hw : IsSquare (normW x y)) :
    IsSquare (radiusSq x y) := by
  have hN : 0<(2*x)^2+(2*y)^2 := by dsimp [radiusSq] at hs; nlinarith
  have h1 : ((2*x)^2+(radiusSq x y-1)^2)/((2*x)^2+(2*y)^2)=normZ x y := by
    dsimp [normZ,radiusSq]
    congr 1 <;> ring
  have h2 : ((2*y)^2+(radiusSq x y-1)^2)/((2*x)^2+(2*y)^2)=normW x y := by
    dsimp [normW,radiusSq]
    congr 1 <;> ring
  have hh := common_faces_square (2*x) (2*y) (radiusSq x y-1) hN
    (h1 ▸ hz) (h2 ▸ hw) (by rw [sphere_identity]; exact IsSquare.sq _)
  have he : ((2*x)^2+(2*y)^2)/4=radiusSq x y := by dsimp [radiusSq]; ring
  rw [← he]
  exact hh.div (show IsSquare (4 : ℚ) from ⟨2,by norm_num⟩)

lemma face_squares_of_norms (x y : ℚ) (hs : 0<radiusSq x y)
    (hz : IsSquare (normZ x y)) (hw : IsSquare (normW x y)) :
    IsSquare ((2*x)^2+(2*y)^2) ∧
    IsSquare ((2*x)^2+(radiusSq x y-1)^2) ∧
    IsSquare ((2*y)^2+(radiusSq x y-1)^2) := by
  have hden : 4*radiusSq x y ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hs)
  have h4 : IsSquare (4*radiusSq x y) :=
    (show IsSquare (4 : ℚ) from ⟨2,by norm_num⟩).mul (radius_square_of_norms x y hs hz hw)
  refine ⟨?_,?_,?_⟩
  · convert h4 using 1
    dsimp [radiusSq]
    ring
  · have hh := hz.mul h4
    dsimp [normZ] at hh
    rw [div_mul_cancel₀ _ hden] at hh
    convert hh using 1
    ring
  · have hh := hw.mul h4
    dsimp [normW] at hh
    rw [div_mul_cancel₀ _ hden] at hh
    convert hh using 1
    ring

theorem perfectCuboid_of_norms (x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hs : radiusSq x y ≠ 1) (hz : IsSquare (normZ x y)) (hw : IsSquare (normW x y)) :
    RationalPerfectCuboid := by
  have hs0 : 0<radiusSq x y := by dsimp [radiusSq]; positivity
  obtain ⟨h1,h2,h3⟩ := face_squares_of_norms x y hs0 hz hw
  refine ⟨|2*x|,|2*y|,|radiusSq x y-1|,
    abs_pos.mpr (mul_ne_zero (by norm_num) hx),
    abs_pos.mpr (mul_ne_zero (by norm_num) hy),
    abs_pos.mpr (sub_ne_zero.mpr hs),?_,?_,?_,?_⟩
  · simpa only [sq_abs] using h1
  · simpa only [sq_abs] using h2
  · simpa only [sq_abs] using h3
  · simp only [sq_abs,sphere_identity]
    exact IsSquare.sq _

/-- Conversely, stereographic projection of a rational perfect cuboid supplies
nondegenerate parameters satisfying the two norm conditions. -/
theorem norm_parameters_of_perfectCuboid (h : RationalPerfectCuboid) :
    ∃ x y : ℚ, x ≠ 0 ∧ y ≠ 0 ∧ radiusSq x y ≠ 1 ∧
      IsSquare (normZ x y) ∧ IsSquare (normW x y) := by
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc,hd⟩ := h
  obtain ⟨d,hd⟩ := hd
  let D : ℚ := |d|
  have hD : D^2=a^2+b^2+c^2 := by dsimp [D]; rw [sq_abs]; nlinarith only [hd]
  have hDc : c<D := by have hD0 : 0≤D := abs_nonneg d; nlinarith [sq_pos_of_pos ha]
  have he : D-c ≠ 0 := ne_of_gt (sub_pos.mpr hDc)
  have hplus : D+c ≠ 0 := by linarith
  have hab0 : a^2+b^2 ≠ 0 := by positivity
  let x := a/(D-c)
  let y := b/(D-c)
  have hsum : radiusSq x y=(D+c)/(D-c) := by
    dsimp [radiusSq,x,y]
    field_simp
    linear_combination -hD
  have hxy : x^2+y^2 ≠ 0 := by
    have hh : 0<x := div_pos ha (sub_pos.mpr hDc)
    positivity
  have hzEq : normZ x y=(a^2+c^2)/(a^2+b^2) := by
    dsimp [normZ]
    rw [hsum]
    dsimp [x]
    field_simp [hplus,hab0]
    linear_combination -4*(a^2+c^2)*hD
  have hwEq : normW x y=(b^2+c^2)/(a^2+b^2) := by
    dsimp [normW]
    rw [hsum]
    dsimp [y]
    field_simp [hplus,hab0]
    linear_combination -4*(b^2+c^2)*hD
  refine ⟨x,y,div_ne_zero (ne_of_gt ha) he,div_ne_zero (ne_of_gt hb) he,?_,?_,?_⟩
  · rw [hsum]
    intro hh
    have hh' := (div_eq_one_iff_eq he).mp hh
    linarith
  · rw [hzEq]; exact hac.div hab
  · rw [hwEq]; exact hbc.div hab

theorem perfectCuboid_iff_norm_parameters : RationalPerfectCuboid ↔
    ∃ x y : ℚ, x ≠ 0 ∧ y ≠ 0 ∧ radiusSq x y ≠ 1 ∧
      IsSquare (normZ x y) ∧ IsSquare (normW x y) := by
  constructor
  · exact norm_parameters_of_perfectCuboid
  · rintro ⟨x,y,hx,hy,hs,hz,hw⟩
    exact perfectCuboid_of_norms x y hx hy hs hz hw

/-- Cartesian components of the two complex Pythagorean parameters. -/
def zRe (x y : ℚ) : ℚ := x*(radiusSq x y+1)/(2*radiusSq x y)
def zIm (x y : ℚ) : ℚ := y*(radiusSq x y-1)/(2*radiusSq x y)
def wRe (x y : ℚ) : ℚ := y*(radiusSq x y+1)/(2*radiusSq x y)
def wIm (x y : ℚ) : ℚ := -x*(radiusSq x y-1)/(2*radiusSq x y)

def qpoint (x y : ℚ) : ℂ := (x : ℂ)+(y : ℂ)*Complex.I

lemma norm_components (x y : ℚ) (hs : radiusSq x y ≠ 0) :
    (zRe x y)^2+(zIm x y)^2=normZ x y ∧
    (wRe x y)^2+(wIm x y)^2=normW x y := by
  dsimp [zRe,zIm,wRe,wIm,normZ,normW,radiusSq] at hs ⊢
  constructor <;> field_simp <;> ring

lemma pythagorean_components (x y : ℚ) (hs : radiusSq x y ≠ 0) :
    (zRe x y)^2-(zIm x y)^2+(wRe x y)^2-(wIm x y)^2=1 ∧
    zRe x y*zIm x y+wRe x y*wIm x y=0 := by
  dsimp [zRe,zIm,wRe,wIm,radiusSq] at hs ⊢
  constructor <;> field_simp <;> ring

lemma normSq_qpoint (x y : ℚ) : Complex.normSq (qpoint x y)=((x^2+y^2 : ℚ) : ℝ) := by
  simp [qpoint,Complex.normSq_apply,pow_two]

lemma complex_pythagorean (x y : ℚ) (hs : radiusSq x y ≠ 0) :
    (qpoint (zRe x y) (zIm x y))^2+(qpoint (wRe x y) (wIm x y))^2=1 := by
  obtain ⟨h1,h2⟩ := pythagorean_components x y hs
  apply Complex.ext
  · simpa [qpoint,pow_two,sub_eq_add_neg,add_assoc] using
      congrArg ((↑) : ℚ → ℝ) h1
  · have hh := congrArg ((↑) : ℚ → ℝ) h2
    push_cast at hh
    simp only [qpoint,pow_two,Complex.add_im,Complex.mul_im,Complex.add_re,
      Complex.mul_re,Complex.ratCast_re,Complex.ratCast_im,Complex.I_re,Complex.I_im,
      Complex.one_im,mul_zero,mul_one,add_zero,zero_add,sub_zero]
    nlinarith only [hh]

lemma rational_norm_qpoint_iff (x y : ℚ) :
    ‖qpoint x y‖ ∈ Set.range ((↑) : ℚ → ℝ) ↔ IsSquare (x^2+y^2) := by
  have hn : ‖qpoint x y‖^2=((x^2+y^2 : ℚ) : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq,normSq_qpoint]
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨r,?_⟩
    apply Rat.cast_injective (α := ℝ)
    push_cast
    rw [← hr] at hn
    push_cast at hn
    nlinarith only [hn]
  · rintro ⟨r,hr⟩
    refine ⟨|r|,?_⟩
    rw [hr] at hn
    push_cast at hn ⊢
    nlinarith only [hn,sq_abs (r : ℝ),abs_nonneg (r : ℝ),norm_nonneg (qpoint x y)]

/-- Direct connection to the rational-norm conditions on the complex parameters. -/
theorem complex_norms_iff (x y : ℚ) (hs : radiusSq x y ≠ 0) :
    (‖qpoint (zRe x y) (zIm x y)‖ ∈ Set.range ((↑) : ℚ → ℝ) ∧
      ‖qpoint (wRe x y) (wIm x y)‖ ∈ Set.range ((↑) : ℚ → ℝ)) ↔
    (IsSquare (normZ x y) ∧ IsSquare (normW x y)) := by
  rw [rational_norm_qpoint_iff,rational_norm_qpoint_iff,
    (norm_components x y hs).1,(norm_components x y hs).2]

/-- Degenerate parameters satisfy both conditions; positivity of all three box
edges cannot be omitted. -/
lemma degenerate_controls :
    (IsSquare (normZ (3/4) 0) ∧ IsSquare (normW (3/4) 0)) ∧
    (IsSquare (normZ 0 (3/4)) ∧ IsSquare (normW 0 (3/4))) ∧
    (IsSquare (normZ (3/5) (4/5)) ∧ IsSquare (normW (3/5) (4/5))) := by
  norm_num [normZ,normW,radiusSq]

#print axioms radius_square_of_norms
#print axioms perfectCuboid_of_norms
#print axioms perfectCuboid_iff_norm_parameters
#print axioms complex_pythagorean
#print axioms complex_norms_iff
#print axioms degenerate_controls
end Erdos213.DivisionCuboid
