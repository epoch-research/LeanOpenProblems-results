import FormalConjectures.Util.ProblemImports
open SetTheory
#check (0 : PGame)
#check PGame.le_iff_sub_nonneg
#check PGame.lt_iff_sub_pos
#check lt_irrefl
example : ¬ ((0 : PGame) < 0) := lt_irrefl _
-- Try deriving a contradiction from lt iff sub pos on zero.
example : ¬ (0 < (0 : PGame) - 0) := by
  have h : (0 : PGame) - 0 = 0 := by simp
  simpa [h] using (lt_irrefl (0 : PGame))
