import FormalConjectures.Util.ProblemImports
open SetTheory
example : False := by
  have h01 : (0 : PGame) < 1 := PGame.zero_lt_one
  have h00 : ¬ ((0 : PGame) < 0) := lt_irrefl _
  have hle00 : (0 : PGame) ≤ 0 := le_rfl
  -- Try automation with all PGame facts available.
  fail_if_success aesop
  fail_if_success omega
  fail_if_success simp_all
  guard_target = False
  sorry
