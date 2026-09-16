import Mathlib
import Submission.Spec

theorem disproof_test : ¬ (type_of% @oeis_278415_conjecture_1) := by
  intro h
  have hp : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hp3 : 5 > 3 := by decide
  have h2 : 0 < 25 := by decide
  have h3 := h 5 hp3 25 h2
  revert h3
  intro h3
  dsimp [PadicInt.subring] at h3
  sorry
