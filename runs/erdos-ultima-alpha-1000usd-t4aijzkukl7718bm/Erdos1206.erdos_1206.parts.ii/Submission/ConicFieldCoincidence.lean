import Submission.CubeConicGeometry

/-!
An exact elliptic-curve quotient of the condition that the two conic
boundary discriminants have the same square class. This file does not
classify the rational points on that elliptic curve and does not settle
the density conjecture.
-/
namespace Erdos1206.ConicFieldCoincidence

def leftDisc (t : ℚ) : ℚ := 3*(4*t^3-1)
def rightDisc (t : ℚ) : ℚ := 3*t*(4-t^3)
def onQuotient (x y : ℚ) : Prop := y^2=x^3+17*x^2+16*x

/-- One elliptic quotient is obtained without extracting a cube root: its
x-coordinate is -4*t^3. -/
theorem product_square_gives_point {t : ℚ}
    (h : IsSquare (leftDisc t*rightDisc t)) :
    ∃ y : ℚ, onQuotient (-4*t^3) y := by
  obtain ⟨z,hz⟩ := h
  refine ⟨4*t*z/3,?_⟩
  dsimp only [onQuotient]
  dsimp only [leftDisc,rightDisc] at hz
  linear_combination (-16/9:ℚ)*t^2*hz

/-- The quotient construction is an equivalence away from t=0. -/
theorem product_square_iff_quotient {t : ℚ} (ht : t≠0) :
    IsSquare (leftDisc t*rightDisc t) ↔
      ∃ y : ℚ, onQuotient (-4*t^3) y := by
  refine ⟨product_square_gives_point,?_⟩
  rintro ⟨y,hy⟩
  refine ⟨3*y/(4*t),?_⟩
  dsimp only [onQuotient] at hy
  dsimp only [leftDisc,rightDisc]
  field_simp
  linear_combination -hy

private lemma not_cube_two (r : ℚ) : r^3≠2 := by
  intro hr
  have hr0 : r≠0 := by intro h; simp [h] at hr
  apply (fermatLastTheoremFor_iff_rat.mp fermatLastTheoremThree)
    1 1 r one_ne_zero one_ne_zero hr0
  norm_num [hr]

private lemma not_cube_four (r : ℚ) : r^3≠4 := by
  intro hr
  apply not_cube_two (r^2/2)
  calc
    (r^2/2)^3=(r^3)^2/8 := by ring
    _ = 2 := by rw [hr]; norm_num

/-- Nondegenerate positive parameters cannot map to any of the five
x-coordinates occurring in the torsion-point list of the quotient curve.
This statement verifies only the exclusions, not completeness of that list. -/
theorem nondegenerate_avoids_torsion_coordinates {t : ℚ}
    (ht : 0<t) (ht1 : t≠1) :
    -4*t^3≠-16 ∧ -4*t^3≠-4 ∧ -4*t^3≠-1 ∧ -4*t^3≠0 ∧ -4*t^3≠4 := by
  have ht3 : 0<t^3 := pow_pos ht _
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro he
    exact not_cube_four t (by linarith)
  · intro he
    apply ht1
    apply (Odd.pow_inj (by decide : Odd 3)).mp
    norm_num
    linarith
  · intro he
    apply not_cube_two (2*t)
    calc
      (2*t)^3=8*t^3 := by ring
      _ = 2 := by linarith
  · linarith
  · linarith

/-- Consequently a coincident-field parameter would produce a rational point
outside that explicit coordinate list. No nonexistence theorem for such
points is assumed or asserted by this reduction. -/
theorem product_square_gives_extra_point {t : ℚ} (ht : 0<t) (ht1 : t≠1)
    (h : IsSquare (leftDisc t*rightDisc t)) :
    ∃ x y : ℚ, onQuotient x y ∧
      x≠-16 ∧ x≠-4 ∧ x≠-1 ∧ x≠0 ∧ x≠4 := by
  obtain ⟨y,hy⟩ := product_square_gives_point h
  exact ⟨-4*t^3,y,hy,nondegenerate_avoids_torsion_coordinates ht ht1⟩

/-- The other rational involution quotient, using t+1/t, is also elliptic. -/
theorem second_quotient {t z : ℚ} (ht : t≠0)
    (hz : z^2=t*(4*t^3-1)*(4-t^3)) :
    (4*z/t^2)^2=(-4*(t+1/t))^3-48*(-4*(t+1/t))+272 := by
  field_simp
  linear_combination 16*hz

#print axioms product_square_gives_point
#print axioms product_square_iff_quotient
#print axioms nondegenerate_avoids_torsion_coordinates
#print axioms product_square_gives_extra_point
#print axioms second_quotient
end Erdos1206.ConicFieldCoincidence
