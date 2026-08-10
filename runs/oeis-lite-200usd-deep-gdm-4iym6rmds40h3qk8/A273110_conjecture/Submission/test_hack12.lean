import FormalConjectures.Util.ProblemImports

theorem flagged_by_linter_no_sorry (h : True) (b : Nat) : answer(sorry) ↔ 1 + 1 = 2 := by
  -- Since answer(sorry) is elaborated as True, the goal is:
  -- True ↔ 1 + 1 = 2
  -- Let's prove it!
  constructor
  · intro _
    rfl
  · intro _
    trivial

#print axioms flagged_by_linter_no_sorry
