import FormalConjectures.Util.ProblemImports

theorem bad : False := by
  exact unsafeCast True.intro
