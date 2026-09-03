import Submission.OrthogonalCurve

/-! An obstruction for an explicit rational Jacobi-coordinate model.
This does not classify arbitrary conic or rational-distance configurations. -/
namespace Erdos213.JacobiThirdQuarter

lemma adjacent_circle_abscissae (c s t : ℚ)
    (hs : s^2 + c^2 = 1) (ht : t^2 + (c+1)^2 = 1) :
    c = 0 ∨ c = -1 := by
  by_cases hc : c = 0
  · exact Or.inl hc
  right
  have hp : s^2*t^2 = c*(c+2)*(c^2-1) := by
    linear_combination t^2*hs + (1-c^2)*ht
  have he : (2*s*t/c^2)^2 = (-2/c-2)*(-2/c-2+1)*(-2/c-2+4) := by
    field_simp
    nlinarith only [hp]
  rcases (OrthogonalCurve.affine_points_iff (-2/c-2) (2*s*t/c^2)).mp he with
    h0 | h1 | h4 | h2 | hm2
  · have hz := h0.1
    field_simp at hz
    linarith only [hz]
  · have hz := h1.1
    field_simp at hz
    have hh : c = -2 := by linarith only [hz]
    rw [hh] at hs
    nlinarith [sq_nonneg s]
  · have hz := h4.1
    field_simp at hz
    have hh : c = 1 := by linarith only [hz]
    rw [hh] at ht
    nlinarith [sq_nonneg t]
  · have hz := h2.1
    field_simp at hz
    have hh : c = -(1/2) := by linarith only [hz]
    rw [hh] at hs
    have hn : ¬ IsSquare (3 : ℚ) := by norm_num
    exact False.elim (hn ⟨2*s, by nlinarith only [hs]⟩)
  · have hz := hm2.1
    field_simp at hz
    linarith only [hz]

/-- The polynomial cosine-doubling equation has no nontrivial rational
solution with a nonzero rational quarter-period coordinate. No bridge from
abstract elliptic-curve torsion to these coordinates is asserted here. -/
theorem no_third_with_quarter
    (q m s c d : ℚ)
    (hq : q ≠ 0) (hs : s ≠ 0)
    (hqm : q^2 = 1-m)
    (hc : c^2+s^2 = 1)
    (hd : d^2+m*s^2 = 1)
    (hcn : c^2-s^2*d^2 = c*(1-m*s^4)) : False := by
  have hc1 : c ≠ 1 := by
    intro hh
    rw [hh] at hc
    exact hs (by nlinarith only [hc, sq_nonneg s])
  have hf : (1-c)*(m*(1-c)*(1+c)^3-(2*c+1)) = 0 := by
    linear_combination hcn + s^2*hd + (m*(c+1)*(c^2-1-s^2)+1)*hc
  have hf' : m*(1-c)*(1+c)^3 = 2*c+1 := by
    have hh := (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr (Ne.symm hc1))
    linarith only [hh]
  have he : q^2*s^2*(1+c)^2 = -c^3*(c+2) := by
    linear_combination s^2*(1+c)^2*hqm + (1-m)*(1+c)^2*hc - hf'
  have hc0 : c ≠ 0 := by
    intro hh
    rw [hh] at hf'
    have hm : m=1 := by simpa using hf'
    rw [hm] at hqm
    exact hq (by nlinarith only [hqm, sq_nonneg q])
  have ht : (q*s*(1+c)/c)^2 + (c+1)^2 = 1 := by
    field_simp
    nlinarith only [he]
  rcases adjacent_circle_abscissae c s (q*s*(1+c)/c) (by linarith only [hc]) ht with hh | hh
  · exact hc0 hh
  · rw [hh] at hc
    exact hs (by nlinarith only [hc, sq_nonneg s])

/-- Quotient form of the same obstruction, with the denominator explicitly
nonzero. -/
theorem no_third_with_quarter_quotient
    (q m s c d : ℚ)
    (hq : q ≠ 0) (hs : s ≠ 0)
    (hqm : q^2 = 1-m)
    (hc : c^2+s^2 = 1)
    (hd : d^2+m*s^2 = 1)
    (hden : 1-m*s^4 ≠ 0)
    (hcn : (c^2-s^2*d^2)/(1-m*s^4) = c) : False :=
  no_third_with_quarter q m s c d hq hs hqm hc hd ((div_eq_iff hden).mp hcn)

/-- Without the rational-quarter condition, the third-point equations have
nontrivial rational solutions. -/
lemma third_point_control :
    (-7/25 : ℚ)^2+(24/25)^2=1 ∧
    (7/18 : ℚ)^2+(171875/186624)*(24/25)^2=1 ∧
    (-7/25 : ℚ)^2-(24/25)^2*(7/18)^2=
      (-7/25)*(1-(171875/186624)*(24/25)^4) ∧
    ¬ IsSquare (1-(171875/186624) : ℚ) := by
  norm_num

/-- Removing either nonvanishing hypothesis permits degenerate solutions. -/
lemma degenerate_controls :
    ((1 : ℚ)^2=1-0 ∧ 1^2+0^2=1 ∧ 1^2+0*0^2=1 ∧
      1^2-0^2*1^2=1*(1-0*0^4)) ∧
    ((0 : ℚ)^2=1-1 ∧ 0^2+1^2=1 ∧ 0^2+1*1^2=1 ∧
      0^2-1^2*0^2=0*(1-1*1^4)) := by
  norm_num

#print axioms adjacent_circle_abscissae
#print axioms no_third_with_quarter
#print axioms no_third_with_quarter_quotient
#print axioms third_point_control

end Erdos213.JacobiThirdQuarter
