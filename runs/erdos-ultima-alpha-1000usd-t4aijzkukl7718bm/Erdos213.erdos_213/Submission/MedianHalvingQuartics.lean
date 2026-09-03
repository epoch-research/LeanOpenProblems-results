import Submission.IsoscelesCurve

/-! Two quartic obstructions for a selected median-fibration halving coset.
These results do not classify arbitrary rational-distance configurations. -/
namespace Erdos213.MedianHalvingQuartics
set_option maxHeartbeats 2000000

lemma first_quartic {r q : ℚ} (h : q^2 = r^4 + 34*r^2 + 1) :
    r = 0 ∨ r^2 = 1 := by
  by_cases hr : r = 0
  · exact Or.inl hr
  right
  let x : ℚ := (q + 1 - r^2) / (2*r^2)
  have hx : r^2*x*(x+1) = x+9 := by
    dsimp [x]
    field_simp
    nlinarith only [h]
  have he : (r*x*(x+1))^2 = x*(x+1)*(x+9) := by
    linear_combination x*(x+1)*hx
  rcases IsoscelesCurve.plus_curve_abscissa he with h | h | h | h | h
  all_goals rw [h] at hx
  all_goals nlinarith [sq_pos_of_ne_zero hr]

lemma second_quartic {r q : ℚ} (h : q^2 = 9*r^4 - 14*r^2 + 9) :
    r = 0 ∨ r^2 = 1 := by
  by_cases hr : r = 0
  · exact Or.inl hr
  right
  let x : ℚ := 3*(q + 3 - 3*r^2) / (2*r^2)
  have hx : r^2*x*(x+9) = 9*(x+1) := by
    dsimp [x]
    field_simp
    nlinarith only [h]
  have he : (r*x*(x+9)/3)^2 = x*(x+1)*(x+9) := by
    linear_combination x*(x+9)/9*hx
  rcases IsoscelesCurve.plus_curve_abscissa he with h | h | h | h | h
  all_goals rw [h] at hx
  all_goals nlinarith [sq_pos_of_ne_zero hr]

lemma first_square_iff (r : ℚ) :
    IsSquare (r^4 + 34*r^2 + 1) ↔ r = 0 ∨ r^2 = 1 := by
  constructor
  · rintro ⟨q,hq⟩
    apply first_quartic (q := q)
    nlinarith only [hq]
  · rintro (rfl | h)
    · norm_num
    · have h4 : r^4 = 1 := by rw [show r^4 = (r^2)^2 by ring,h]; norm_num
      rw [h4,h]
      norm_num

lemma second_square_iff (r : ℚ) :
    IsSquare (9*r^4 - 14*r^2 + 9) ↔ r = 0 ∨ r^2 = 1 := by
  constructor
  · rintro ⟨q,hq⟩
    apply second_quartic (q := q)
    nlinarith only [hq]
  · rintro (rfl | h)
    · norm_num
    · have h4 : r^4 = 1 := by rw [show r^4 = (r^2)^2 by ring,h]; norm_num
      rw [h4,h]
      norm_num

lemma nonsingular_halving_obstruction {k : ℚ}
    (h₀ : k ≠ 0) (h₁ : k ≠ -1) (h₂ : k ≠ -2) :
    ¬ IsSquare ((k+1)^4 + 34*(k+1)^2 + 1) ∧
    ¬ IsSquare (9*(k+1)^4 - 14*(k+1)^2 + 9) := by
  have h : ¬ (k+1 = 0 ∨ (k+1)^2 = 1) := by
    rintro (h | h)
    · apply h₁; linarith
    · have hz : k*(k+2) = 0 := by nlinarith only [h]
      rcases mul_eq_zero.mp hz with h | h
      · exact h₀ h
      · apply h₂; linarith
  exact ⟨fun hs => h ((first_square_iff _).mp hs),
    fun hs => h ((second_square_iff _).mp hs)⟩

#print axioms first_square_iff
#print axioms second_square_iff
#print axioms nonsingular_halving_obstruction

/-- The explicit square-x section cannot be the double of an affine rational point.
The statement uses the cleared duplication equation, so no group-law API or
external Mordell-Weil calculation is needed. -/
lemma no_selected_double {r x y : ℚ} (hr : r ≠ 0) (hr₁ : r^2 ≠ 1)
    (hcurve : y^2 = x^3 + 9*(r^2+1)^2*x^2 - 576*r^2*(r^2-1)^2*x) :
    (x^2 + 576*r^2*(r^2-1)^2)^2 ≠
      4*y^2*((r^2-1)*(9*r^2+1)/(2*r))^2 := by
  let A : ℚ := 9*(r^2+1)^2
  let B : ℚ := -576*r^2*(r^2-1)^2
  let v : ℚ := (r^2-1)*(9*r^2+1)/(2*r)
  let m : ℚ := -(r^2-1)*(9*r^4+26*r^2+1)/(2*r^2)
  let p : ℚ := 9*(r^2-1)*(3*r^2-1)^2/2
  have hv : v ≠ 0 := by
    dsimp [v]
    apply div_ne_zero
    · apply mul_ne_zero (sub_ne_zero.mpr hr₁)
      nlinarith [sq_nonneg r]
    · exact mul_ne_zero (by norm_num) hr
  have hm : m^2-B = (v/r)^2*(r^4+34*r^2+1) := by
    dsimp [m,B,v]
    field_simp
    ring
  have hp : p^2-B = (3*r*v)^2*(9*r^4-14*r^2+9) := by
    dsimp [p,B,v]
    field_simp
    ring
  have hf : (x^2-2*m*x+B)*(x^2-2*p*x+B) =
      (x^2-B)^2 - 4*v^2*(x^3+A*x^2+B*x) := by
    dsimp [m,p,B,v,A]
    field_simp
    ring
  intro hd
  have hd' : (x^2-B)^2 = 4*y^2*v^2 := by
    dsimp [B,v]
    convert hd using 1 <;> ring
  have hc : y^2 = x^3+A*x^2+B*x := by
    dsimp [A,B]
    linear_combination hcurve
  have hz : (x^2-2*m*x+B)*(x^2-2*p*x+B) = 0 := by
    rw [hf,← hc,hd']
    ring
  rcases mul_eq_zero.mp hz with h | h
  · have he : ((x-m)/(v/r))^2 = r^4+34*r^2+1 := by
      rw [div_pow,div_eq_iff (pow_ne_zero 2 (div_ne_zero hv hr))]
      nlinarith only [h,hm]
    exact (first_quartic he).elim hr hr₁
  · have he : ((x-p)/(3*r*v))^2 = 9*r^4-14*r^2+9 := by
      rw [div_pow,div_eq_iff (pow_ne_zero 2
        (mul_ne_zero (mul_ne_zero (by norm_num) hr) hv))]
      nlinarith only [h,hp]
    exact (second_quartic he).elim hr hr₁

#print axioms no_selected_double

end Erdos213.MedianHalvingQuartics
