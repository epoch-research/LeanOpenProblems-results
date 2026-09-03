import Submission.OrthogonalGlobal

/-! Rational-point classification for the conductor-24 curve used in the
orthogonal-grid investigation. This is not a classification of arbitrary
rational-distance sets. The proof uses explicit duplication identities and
the elementary descent in `OrthogonalGlobal`. -/
namespace Erdos213.OrthogonalCurve

lemma duplication_squares {x y : ℚ} (hy : y ≠ 0)
    (h : y^2=x*(x+1)*(x+4)) :
    IsSquare (((x^2-4)/(2*y))^2+1) ∧
    IsSquare (((x^2-4)/(2*y))^2+4) := by
  constructor
  · refine ⟨(x^2+2*x+4)/(2*y),?_⟩
    field_simp
    nlinarith only [h]
  · refine ⟨(x^2+8*x+4)/(2*y),?_⟩
    field_simp
    nlinarith only [h]

lemma abscissa_of_nonzero_ordinate {x y : ℚ} (hy : y ≠ 0)
    (h : y^2=x*(x+1)*(x+4)) : x=2 ∨ x= -2 := by
  have hz := (OrthogonalGlobal.simultaneous_squares_iff_zero
    ((x^2-4)/(2*y))).mp (duplication_squares hy h)
  have hn : x^2-4=0 := (div_eq_zero_iff.mp hz).resolve_right (mul_ne_zero (by norm_num) hy)
  have hf : (x-2)*(x+2)=0 := by nlinarith only [hn]
  rcases mul_eq_zero.mp hf with hf | hf
  · left; linarith only [hf]
  · right; linarith only [hf]

/-- The complete affine rational point list. No elliptic-curve rank or torsion
computation is used as an unproved input. -/
theorem affine_points_iff (x y : ℚ) :
    y^2=x*(x+1)*(x+4) ↔
    (x=0 ∧ y=0) ∨ (x= -1 ∧ y=0) ∨ (x= -4 ∧ y=0) ∨
    (x=2 ∧ (y=6 ∨ y= -6)) ∨ (x= -2 ∧ (y=2 ∨ y= -2)) := by
  constructor
  · intro h
    by_cases hy : y=0
    · subst y
      have hh : x*(x+1)*(x+4)=0 := by simpa using h.symm
      rcases mul_eq_zero.mp hh with hh | hh
      · rcases mul_eq_zero.mp hh with hh | hh
        · exact Or.inl ⟨hh,rfl⟩
        · exact Or.inr (Or.inl ⟨by linarith only [hh],rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨by linarith only [hh],rfl⟩))
    · rcases abscissa_of_nonzero_ordinate hy h with hx | hx
      · right; right; right; left
        refine ⟨hx,?_⟩
        have hf : (y-6)*(y+6)=0 := by rw [hx] at h; nlinarith only [h]
        rcases mul_eq_zero.mp hf with hf | hf
        · left; linarith only [hf]
        · right; linarith only [hf]
      · right; right; right; right
        refine ⟨hx,?_⟩
        have hf : (y-2)*(y+2)=0 := by rw [hx] at h; nlinarith only [h]
        rcases mul_eq_zero.mp hf with hf | hf
        · left; linarith only [hf]
        · right; linarith only [hf]
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
      ⟨rfl,rfl | rfl⟩ | ⟨rfl,rfl | rfl⟩) <;> norm_num

#print axioms duplication_squares
#print axioms affine_points_iff

lemma square_abscissa_zero {u v : ℚ} (h : v^2=u^2*(u^2+1)*(u^2+4)) : u=0 := by
  have htwo : ¬ IsSquare (2 : ℚ) := by norm_num
  rcases (affine_points_iff (u^2) v).mp h with h0 | h1 | h4 | h2 | hm2
  · nlinarith only [h0.1, sq_nonneg u]
  · nlinarith only [h1.1, sq_nonneg u]
  · nlinarith only [h4.1, sq_nonneg u]
  · exact False.elim (htwo ⟨u,by simpa only [pow_two] using h2.1.symm⟩)
  · nlinarith only [hm2.1, sq_nonneg u]

lemma isogenous_image {x y : ℚ} (hx : x ≠ 0)
    (h : y^2=x*(x-1)*(x-9)) :
    (y*(9-x^2)/(8*x^2))^2 =
      ((x^2-10*x+9)/(4*x))*(((x^2-10*x+9)/(4*x))+1)*
      (((x^2-10*x+9)/(4*x))+4) := by
  field_simp
  linear_combination 64*(x^2-9)^2*h

/-- Affine rational points on the two-isogenous model. -/
theorem isogenous_affine_points_iff (x y : ℚ) :
    y^2=x*(x-1)*(x-9) ↔ (x=0 ∨ x=1 ∨ x=9) ∧ y=0 := by
  constructor
  · intro h
    have hy : y=0 := by
      by_cases hx : x=0
      · rw [hx] at h
        nlinarith only [h]
      · have him := isogenous_image hx h
        have he : (x^2-10*x+9)/(4*x)=(y/(2*x))^2 := by
          field_simp
          nlinarith only [h]
        rw [he] at him
        have hz := square_abscissa_zero him
        exact (div_eq_zero_iff.mp hz).resolve_right (mul_ne_zero (by norm_num) hx)
    refine ⟨?_,hy⟩
    rw [hy] at h
    have hf : x*(x-1)*(x-9)=0 := by simpa using h.symm
    rcases mul_eq_zero.mp hf with hf | hf
    · rcases mul_eq_zero.mp hf with hf | hf
      · exact Or.inl hf
      · exact Or.inr (Or.inl (by linarith only [hf]))
    · exact Or.inr (Or.inr (by linarith only [hf]))
  · rintro ⟨rfl | rfl | rfl,rfl⟩ <;> norm_num

#print axioms isogenous_affine_points_iff
end Erdos213.OrthogonalCurve
