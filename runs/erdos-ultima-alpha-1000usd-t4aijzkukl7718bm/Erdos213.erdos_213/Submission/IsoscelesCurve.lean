import Submission.IsoscelesMedians

/-! Rational isosceles triangles with all three rational medians are degenerate.
The proof uses the elementary descent, not an external elliptic rank. -/
namespace Erdos213.IsoscelesCurve
set_option maxHeartbeats 2000000

lemma minus_curve_ordinate_zero {x y : ℚ}
    (h : y^2=x*(x-1)*(x-4)) : y=0 := by
  by_contra hy
  apply IsoscelesMedians.no_three_four ((x^2-8*x+4)/(2*y))
  constructor
  · refine ⟨(x^2-2*x+4)/(2*y),?_⟩
    field_simp
    nlinarith only [h]
  · refine ⟨(x^2-4)/(2*y),?_⟩
    field_simp
    nlinarith only [h]

lemma minus_curve_points (x y : ℚ) :
    y^2=x*(x-1)*(x-4) ↔ (x=0 ∨ x=1 ∨ x=4) ∧ y=0 := by
  constructor
  · intro h
    have hy := minus_curve_ordinate_zero h
    refine ⟨?_,hy⟩
    rw [hy] at h
    have hh : x*(x-1)*(x-4)=0 := by linarith
    rcases mul_eq_zero.mp hh with hh | hh
    · rcases mul_eq_zero.mp hh with hh | hh
      · exact Or.inl hh
      · right; left; linarith
    · right; right; linarith
  · rintro ⟨rfl | rfl | rfl,rfl⟩ <;> norm_num

lemma isogenous_image {x y : ℚ} (hx : x≠0)
    (h : y^2=x*(x+1)*(x+9)) :
    (y*(9-x^2)/(8*x^2))^2 =
      ((x^2+10*x+9)/(4*x))*(((x^2+10*x+9)/(4*x))-1)*
      (((x^2+10*x+9)/(4*x))-4) := by
  field_simp
  linear_combination 64*(x^2-9)^2*h

lemma plus_curve_abscissa {x y : ℚ} (h : y^2=x*(x+1)*(x+9)) :
    x=0 ∨ x= -1 ∨ x= -9 ∨ x=3 ∨ x= -3 := by
  by_cases hy : y=0
  · rw [hy] at h
    have hh : x*(x+1)*(x+9)=0 := by linarith
    rcases mul_eq_zero.mp hh with hh | hh
    · rcases mul_eq_zero.mp hh with hh | hh
      · exact Or.inl hh
      · right; left; linarith
    · right; right; left; linarith
  · have hx : x≠0 := by intro hx; rw [hx] at h; norm_num at h; exact hy h
    have hz := minus_curve_ordinate_zero (isogenous_image hx h)
    have he : 9-x^2=0 := by
      have hn := (div_eq_zero_iff.mp hz).resolve_right (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx))
      exact (mul_eq_zero.mp hn).resolve_left hy
    have hf : (x-3)*(x+3)=0 := by nlinarith only [he]
    rcases mul_eq_zero.mp hf with hf | hf
    · right; right; right; left; linarith
    · right; right; right; right; linarith

lemma normalized_isosceles {t u v : ℚ}
    (hu : u^2=1+2*t^2) (hv : v^2=4-t^2) : t=0 ∨ t^2=4 := by
  have he : (2*t*u*v)^2=(-1-2*t^2)*((-1-2*t^2)+1)*((-1-2*t^2)+9) := by
    rw [mul_pow,mul_pow,mul_pow,hu,hv]
    ring
  rcases plus_curve_abscissa he with h | h | h | h | h
  · nlinarith [sq_nonneg t]
  · left; nlinarith [sq_nonneg t]
  · right; linarith
  · nlinarith [sq_nonneg t]
  · have ht : t^2=1 := by linarith
    have hs : IsSquare (3 : ℚ) := ⟨u,by rw [ht] at hu; nlinarith only [hu]⟩
    norm_num at hs

lemma isosceles_heron_zero {a b c : ℚ} (hab : a^2=b^2)
    (h₁ : IsSquare (2*b^2+2*c^2-a^2)) (h₂ : IsSquare (2*a^2+2*b^2-c^2)) :
    2*a^2*b^2+2*a^2*c^2+2*b^2*c^2-a^4-b^4-c^4=0 := by
  obtain ⟨u,hu⟩ := h₁
  obtain ⟨v,hv⟩ := h₂
  have hu' : u^2=a^2+2*c^2 := by nlinarith only [hu,hab]
  have hv' : v^2=4*a^2-c^2 := by nlinarith only [hv,hab]
  by_cases ha : a=0
  · rw [ha] at hv'
    have hc : c=0 := by nlinarith [sq_nonneg v,sq_nonneg c]
    rw [ha] at hab
    have hb : b=0 := by nlinarith [sq_nonneg b]
    simp [ha,hb,hc]
  · have hU : (u/a)^2=1+2*(c/a)^2 := by field_simp; nlinarith only [hu']
    have hV : (v/a)^2=4-(c/a)^2 := by field_simp; nlinarith only [hv']
    rcases normalized_isosceles hU hV with hc | hc
    · have hc' : c=0 := (div_eq_zero_iff.mp hc).resolve_right ha
      rw [hc',show a^4=(a^2)^2 by ring,show b^4=(b^2)^2 by ring,← hab]
      ring
    · have hc' : c^2=4*a^2 := by field_simp at hc; nlinarith only [hc]
      rw [show a^4=(a^2)^2 by ring,show b^4=(b^2)^2 by ring,
        show c^4=(c^2)^2 by ring,← hab,hc']
      ring

#print axioms minus_curve_points
#print axioms plus_curve_abscissa
#print axioms normalized_isosceles
#print axioms isosceles_heron_zero
end Erdos213.IsoscelesCurve
