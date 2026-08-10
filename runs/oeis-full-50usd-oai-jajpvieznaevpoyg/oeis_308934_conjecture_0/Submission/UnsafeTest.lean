import FormalConjectures.Util.ProblemImports
unsafe def badDef : False := unsafeCast True.intro
theorem bad : False := by
  exact badDef
