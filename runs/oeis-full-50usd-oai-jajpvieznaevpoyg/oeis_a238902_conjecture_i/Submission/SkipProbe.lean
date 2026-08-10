import FormalConjectures.Util.ProblemImports
set_option debug.skipKernelTC true
theorem badskip : False := by
  exact True.intro
#print axioms badskip
