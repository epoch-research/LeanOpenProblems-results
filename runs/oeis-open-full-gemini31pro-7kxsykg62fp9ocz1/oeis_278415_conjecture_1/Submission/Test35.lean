import Mathlib
import Submission.Spec

theorem disproof_test : ¬ (type_of% @oeis_278415_conjecture_1) := by
  intro h
  have hp : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hp3 : 5 > 3 := by decide
  have h2 : 0 < 2 := by decide
  have h3 := h 5 hp3 2 h2
  revert h3
  dsimp [PadicInt.subring]
  intro h4
  have h_val : A278415 (5 * 2) = -1200 := by rfl
  have h_val2 : A278415 2 = 0 := by rfl
  -- diff = -1200, den = 100
  -- diff / den = -12
  -- wait, the value is -12, which is an integer! So it IS a 5-adic integer!
  sorry
