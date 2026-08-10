import FormalConjectures.Util.ProblemImports
open SetTheory
#check PGame.zero_le_zero
#check PGame.le_refl
#check PGame.zero_lt_one
#check PGame.not_lt_zero
#check PGame.add_zero
#check PGame.zero_add
#check PGame.sub_self
#check PGame.neg_zero
#check PGame.instPreorder
#check PGame.instLT
example : ((0 : PGame) - 0) = 0 := by simp
example : ¬ (0 < ((0 : PGame) - 0)) := by simp
example : ¬ ((0 : PGame) < 0) := by simp
example : ¬ ((0 : PGame) < 0) := by
  have hiff := (PGame.lt_iff_sub_pos (x:=0) (y:=0))
  simpa using hiff
