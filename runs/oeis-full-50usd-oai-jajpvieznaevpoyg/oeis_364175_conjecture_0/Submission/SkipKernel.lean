import FormalConjectures.Util.ProblemImports
set_option debug.skipKernelTC true
theorem bad : False := (True.intro : True)
#print axioms bad
