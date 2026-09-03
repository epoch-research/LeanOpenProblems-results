import FormalConjecturesUtil
import Submission.FermatArea
import Submission.PythagoreanFibration

/-! Coverage of the norm fibration, not existence of an admissible parameter. -/
namespace Erdos213.PythagoreanFibration

lemma trace_ne_zero {x s : ℚ} (hspos : 0 < s)
    (hs : ∀ i, IsSquare (values x s i)) : x≠0 := by
  intro hx
  obtain ⟨a,ha⟩ := hs 0
  have ha' : s=a^2 := by simpa [values,pow_two] using ha
  have ha0 : a≠0 := by intro hz; simp [hz] at ha'; linarith
  apply FermatArea.quartic_not_square ha0
  convert hs 4 using 1
  dsimp [values]
  rw [hx,ha']
  ring

lemma unit_norm_excluded {x s : ℚ} (harea : x^2 < s)
    (hs : ∀ i, IsSquare (values x s i)) : s≠1 := by
  intro he
  have hdpos : 0 < s+2*x+1 := by nlinarith [sq_nonneg (x+1)]
  have hnpos : 0 < s-2*x+1 := by nlinarith [sq_nonneg (x-1)]
  have hh := rotation_preserves_squares x s (ne_of_gt hdpos) hs
  have hn := trace_ne_zero (div_pos hnpos hdpos) hh
  apply hn
  simp [he]

/-- Every positive-area parameter meeting all six norm-square conditions is
in the rational line pencil. In particular its two excluded symmetry loci
cannot conceal an admissible eight-point witness. -/
lemma admissible_fibration_covers {x s : ℚ} (harea : x^2 < s)
    (hs : ∀ i, IsSquare (values x s i)) :
    ∃ r : ℚ, r≠0 ∧ 1-r^2≠0 ∧ x=r*(1-s)/(1-r^2) :=
  first_fibration_covers (trace_ne_zero (by nlinarith [sq_nonneg x]) hs)
    (unit_norm_excluded harea hs) (hs 3)

lemma negation_values (x s : ℚ) :
    values (-x) s = ![values x s 0,values x s 2,values x s 1,
      values x s 3,values x s 5,values x s 4] := by
  funext i
  fin_cases i <;> dsimp [values] <;> ring

lemma negation_preserves_squares (x s : ℚ) (hs : ∀ i, IsSquare (values x s i)) :
    ∀ i, IsSquare (values (-x) s i) := by
  rw [negation_values]
  intro i
  fin_cases i <;> first | exact hs 0 | exact hs 1 | exact hs 2 | exact hs 3 | exact hs 4 | exact hs 5

lemma inversion_values (x s : ℚ) (hs0 : s≠0) :
    values (x/s) (1/s) = ![1/values x s 0,values x s 1/values x s 0,
      values x s 2/values x s 0,values x s 3/(values x s 0)^2,
      values x s 5/(values x s 0)^2,values x s 4/(values x s 0)^2] := by
  funext i
  fin_cases i <;> dsimp [values] <;> field_simp <;> ring

lemma inversion_preserves_squares (x s : ℚ) (hs0 : s≠0)
    (hs : ∀ i, IsSquare (values x s i)) :
    ∀ i, IsSquare (values (x/s) (1/s) i) := by
  rw [inversion_values x s hs0]
  intro i
  fin_cases i
  · exact IsSquare.one.div (hs 0)
  · exact (hs 1).div (hs 0)
  · exact (hs 2).div (hs 0)
  · exact (hs 3).div (IsSquare.sq _)
  · exact (hs 5).div (IsSquare.sq _)
  · exact (hs 4).div (IsSquare.sq _)

lemma inversion_area (x s : ℚ) (hs0 : s≠0) :
    1/s-(x/s)^2=(s-x^2)/s^2 := by field_simp

#print axioms trace_ne_zero
#print axioms unit_norm_excluded
#print axioms admissible_fibration_covers
#print axioms inversion_preserves_squares
end Erdos213.PythagoreanFibration
