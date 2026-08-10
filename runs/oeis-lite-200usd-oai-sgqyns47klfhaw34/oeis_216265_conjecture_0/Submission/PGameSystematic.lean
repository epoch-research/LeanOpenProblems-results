import FormalConjectures.Util.ProblemImports
open SetTheory
universe u

-- Work at a fixed universe to avoid previous universe mismatch issues.
abbrev G := PGame.{0}

example : (0 : G) < 1 := PGame.zero_lt_one
example : ¬ ((0 : G) < 0) := lt_irrefl _
example : (0 : G) ≤ 0 := le_rfl

example : ((0 : G) ≤ 0) ↔ (0 ≤ ((0 : G) - 0)) := by
  exact PGame.le_iff_sub_nonneg (x := (0 : G)) (y := (0 : G))

example : ((0 : G) < 0) ↔ (0 < ((0 : G) - 0)) := by
  exact PGame.lt_iff_sub_pos (x := (0 : G)) (y := (0 : G))

example : ¬ (0 < ((0 : G) - 0)) := by
  intro h
  exact (lt_irrefl (0 : G)) ((PGame.lt_iff_sub_pos (x := (0 : G)) (y := (0 : G))).2 h)

-- Try some contradiction candidates involving subtraction.
example : ¬ (0 < ((0 : G) - 0) ∧ ((0 : G) ≤ 0)) := by
  intro h
  exact (show ¬ (0 < ((0 : G) - 0)) from by
    intro hp
    exact (lt_irrefl (0 : G)) ((PGame.lt_iff_sub_pos (x := (0 : G)) (y := (0 : G))).2 hp)) h.1

-- Automation should not close False.
example : True := by trivial
