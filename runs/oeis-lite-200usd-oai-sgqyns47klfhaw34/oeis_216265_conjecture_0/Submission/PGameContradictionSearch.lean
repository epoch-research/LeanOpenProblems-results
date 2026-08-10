import FormalConjectures.Util.ProblemImports
open SetTheory

-- Basic facts that do compile.
example : (0 : PGame) < 1 := PGame.zero_lt_one
example : ¬ ((0 : PGame) < 0) := lt_irrefl _
example : (0 : PGame) ≤ 0 := le_rfl

-- Use the source-sorry theorem in simple ways.
example : (0 : PGame) ≤ 0 ↔ 0 ≤ (0 : PGame) - 0 := by
  exact PGame.le_iff_sub_nonneg (x:=0) (y:=0)
example : (0 : PGame) < 0 ↔ 0 < (0 : PGame) - 0 := by
  exact PGame.lt_iff_sub_pos (x:=0) (y:=0)

-- Can we prove or refute 0 < 0 - 0? Should be refutable via iff.
example : ¬ (0 < (0 : PGame) - 0) := by
  intro h
  have hlt : (0 : PGame) < 0 := (PGame.lt_iff_sub_pos (x:=0) (y:=0)).2 h
  exact (lt_irrefl (0 : PGame)) hlt

-- Try standard contradiction candidates.
example : ¬ ((1 : PGame) < 0 ∧ (0 : PGame) < 1) := by
  intro h
  exact not_lt_of_gt h.2 h.1
