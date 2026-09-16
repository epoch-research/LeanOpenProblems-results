import FormalConjectures.Util.ProblemImports

theorem False_of_ZMod (h : 1 ≡ 0 [ZMOD 2]) : False := by
  change 1 % 2 = 0 % 2 at h
  revert h
  decide
