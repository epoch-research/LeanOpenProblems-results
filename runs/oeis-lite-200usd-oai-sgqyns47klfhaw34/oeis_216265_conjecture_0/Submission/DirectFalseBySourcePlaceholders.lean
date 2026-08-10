import FormalConjectures.Util.ProblemImports
-- Try automation with all known source-placeholder theorems in context.
open SetTheory
abbrev G0 := PGame.{0}
example : False := by
  have h1 := (PGame.le_iff_sub_nonneg (x := (0:G0)) (y := (0:G0)))
  have h2 := (PGame.lt_iff_sub_pos (x := (0:G0)) (y := (0:G0)))
  have h3 : (0:G0) < 1 := PGame.zero_lt_one
  have h4 : ¬ ((0:G0) < 0) := lt_irrefl _
  have h5 : (0:G0) ≤ 0 := le_rfl
  fail_if_success exact h4 h3
  fail_if_success exact h4 ((PGame.lt_iff_sub_pos (x := (0:G0)) (y := (0:G0))).2 ?hole)
  guard_target = False
  sorry
