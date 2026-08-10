import FormalConjectures.Util.ProblemImports
open SetTheory

theorem pgame_false_test : False := by
  have h01 : (0 : PGame) < 1 := PGame.zero_lt_one
  have h00 : ¬ ((0 : PGame) < 0) := lt_irrefl _
  have hle00 : (0 : PGame) ≤ 0 := le_rfl
  aesop

#print axioms pgame_false_test
