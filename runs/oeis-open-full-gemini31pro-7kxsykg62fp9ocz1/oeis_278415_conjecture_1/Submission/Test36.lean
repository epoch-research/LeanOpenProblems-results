import Mathlib
import Submission.Spec

theorem test : ¬ (type_of% @oeis_278415_conjecture_1) := by
  intro h
  have hp : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hp3 : 5 > 3 := by decide
  have h2 : 0 < 3 := by decide
  have h3 := h 5 hp3 3 h2
  revert h3
  intro h3
  -- The value for A(15) is 408795
  -- The value for A(3) is -5
  -- diff = 408800
  -- 408800 / 225 = 16352 / 9
  -- We need to check if 16352 / 9 is a 5-adic integer.
  -- 5 doesn't divide 9, so its 5-adic valuation is v(16352) - v(9) = 0 - 0 = 0 >= 0
  -- So it IS a 5-adic integer!
  sorry
