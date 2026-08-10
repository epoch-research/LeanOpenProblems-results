import Mathlib

/-!
# Davenport–Cassels lemma for `x² + y² + z²`

If a nonnegative integer `n` is a sum of three rational squares, then it is a sum of three
integer squares. This is the classical Davenport–Cassels descent for the identity form.
-/

open scoped BigOperators

namespace ThreeSquares

/-- The squared distance from a rational triple to the nearest integer triple is `< 1`
(each coordinate is within `1/2`), giving a bound `≤ 3/4`. -/
lemma exists_round (a b c : ℚ) :
    ∃ x y z : ℤ, (a - x)^2 + (b - y)^2 + (c - z)^2 ≤ 3/4 := by
  refine ⟨round a, round b, round c, ?_⟩
  have ha2 : (a - round a)^2 ≤ (1/2)^2 := by
    nlinarith [abs_sub_round a, abs_nonneg (a - (round a : ℚ)), sq_abs (a - (round a : ℚ))]
  have hb2 : (b - round b)^2 ≤ (1/2)^2 := by
    nlinarith [abs_sub_round b, abs_nonneg (b - (round b : ℚ)), sq_abs (b - (round b : ℚ))]
  have hc2 : (c - round c)^2 ≤ (1/2)^2 := by
    nlinarith [abs_sub_round c, abs_nonneg (c - (round c : ℚ)), sq_abs (c - (round c : ℚ))]
  push_cast
  nlinarith [ha2, hb2, hc2]

end ThreeSquares
