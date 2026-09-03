import Submission.MorleyQuarticDescent

/-! Complete rational-point restrictions for the exceptional circle cubic
of the seven-point quadratic construction, using the existing elementary
descent. This is not an Erdős 213 settlement. -/
namespace Erdos213.HeptadCircleCubic
set_option maxHeartbeats 2000000

lemma doubled_quartic {x y : ℚ} (hy : y≠0)
    (h : y^2=x*(x^2-3*x+3)) :
    ((x^4-6*x^3+18*x^2-18*x+9)/(4*y^2))^2 =
      ((x^2-3)/(2*y))^4-3*((x^2-3)/(2*y))^2+3 := by
  field_simp
  linear_combination 192*(x^4-4*x^3+6*x^2-12*x-4*y^2+9)*h

lemma translated_mordell_abscissa {x y : ℚ}
    (h : y^2=x*(x^2-3*x+3)) : x=0 ∨ x=1 ∨ x=3 := by
  by_cases hy : y=0
  · have hp : 0<x^2-3*x+3 := by nlinarith [sq_nonneg (2*x-3)]
    have hz : x*(x^2-3*x+3)=0 := by rw [hy] at h; nlinarith only [h]
    exact Or.inl ((mul_eq_zero.mp hz).resolve_right (ne_of_gt hp))
  · have hs := MorleyQuarticDescent.rational_quartic (doubled_quartic hy h)
    have he : (x-1)*(x-3)*(x^2+3)=0 := by
      field_simp at hs
      nlinarith only [h,hs]
    have hh := (mul_eq_zero.mp he).resolve_right (by positivity : x^2+3≠0)
    rcases mul_eq_zero.mp hh with h₁ | h₃
    · right; left; linarith
    · right; right; linarith

/-- All rational abscissas on the Mordell curve y^2=x^3+1. -/
theorem mordell_abscissa {x y : ℚ} (h : y^2=x^3+1) : x= -1 ∨ x=0 ∨ x=2 := by
  have he : y^2=(x+1)*((x+1)^2-3*(x+1)+3) := by nlinarith only [h]
  rcases translated_mordell_abscissa he with h₁ | h₀ | h₂
  · left; linarith
  · right; left; linarith
  · right; right; linarith

lemma dual_isogeny {x y : ℚ} (hx : x≠0)
    (h : y^2=x*(x^2+6*x-3)) :
    (y*(-3-x^2)/(8*x^2))^2 =
      ((x^2+6*x-3)/(4*x))*
      (((x^2+6*x-3)/(4*x))^2-3*((x^2+6*x-3)/(4*x))+3) := by
  field_simp
  linear_combination 64*(x^2+3)^2*h

lemma dual_abscissa {x y : ℚ} (h : y^2=x*(x^2+6*x-3)) :
    x=0 ∨ x=1 ∨ x= -3 := by
  by_cases hx : x=0
  · exact Or.inl hx
  · rcases translated_mordell_abscissa (dual_isogeny hx h) with h₀ | h₁ | h₃
    · have hz : x^2+6*x-3=0 := (div_eq_zero_iff.mp h₀).resolve_right (mul_ne_zero (by norm_num) hx)
      have hs : IsSquare (3 : ℚ) := ⟨(x+3)/2,by nlinarith only [hz]⟩
      norm_num at hs
    · have hz : (x-1)*(x+3)=0 := by field_simp at h₁; nlinarith only [h₁]
      rcases mul_eq_zero.mp hz with h | h
      · right; left; linarith
      · right; right; linarith
    · have hz : x^2-6*x-3=0 := by field_simp at h₃; nlinarith only [h₃]
      have hs : IsSquare (3 : ℚ) := ⟨(x-3)/2,by nlinarith only [hz]⟩
      norm_num at hs

def cubic (r s : ℚ) : ℚ :=
  r^3-r^2*s-r^2-r*s^2-r+s^3-s^2-s+1

lemma cubic_to_dual {r s : ℚ} (h : cubic r s=0) :
    (2*(2*(r+s)-1)*(r-s))^2=
      (2*(r+s)-1)*((2*(r+s)-1)^2+6*(2*(r+s)-1)-3) := by
  dsimp [cubic] at h
  linear_combination 8*(2*(r+s)-1)*h

lemma cubic_constraint {r s : ℚ} (h : cubic r s=0) :
    4*(2*(r+s)-1)*(r-s)^2=(2*(r+s)-1)^2+6*(2*(r+s)-1)-3 := by
  dsimp [cubic] at h
  linear_combination 8*h

/-- The four affine rational points of the exceptional circle cubic. -/
theorem cubic_zero_iff (r s : ℚ) :
    cubic r s=0 ↔ (r=0 ∧ s=1) ∨ (r=1 ∧ s=0) ∨ (r=0 ∧ s= -1) ∨ (r= -1 ∧ s=0) := by
  constructor
  · intro h
    have hc := cubic_constraint h
    rcases dual_abscissa (cubic_to_dual h) with h₀ | h₁ | h₃
    · rw [h₀] at hc; norm_num at hc
    · rw [h₁] at hc
      have hs : r+s=1 := by linarith
      have hz : r*s=0 := by nlinarith only [hc,hs,sq_nonneg (r+s-1)]
      rcases mul_eq_zero.mp hz with hr | hs₀
      · left; exact ⟨hr,by linarith⟩
      · right; left; exact ⟨by linarith,hs₀⟩
    · rw [h₃] at hc
      have hs : r+s= -1 := by linarith
      have hz : r*s=0 := by nlinarith only [hc,hs,sq_nonneg (r+s+1)]
      rcases mul_eq_zero.mp hz with hr | hs₀
      · right; right; left; exact ⟨hr,by linarith⟩
      · right; right; right; exact ⟨by linarith,hs₀⟩
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> norm_num [cubic]

theorem cubic_ne_zero_of_positive {r s : ℚ} (hr : 0<r) (hs : 0<s) : cubic r s≠0 := by
  intro h
  rcases (cubic_zero_iff r s).mp h with ⟨h,_⟩ | ⟨_,h⟩ | ⟨h,_⟩ | ⟨_,h⟩ <;> linarith

#print axioms translated_mordell_abscissa
#print axioms mordell_abscissa
#print axioms dual_abscissa
#print axioms cubic_zero_iff
#print axioms cubic_ne_zero_of_positive
end Erdos213.HeptadCircleCubic
