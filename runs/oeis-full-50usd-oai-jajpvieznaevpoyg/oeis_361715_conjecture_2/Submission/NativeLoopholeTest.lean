import FormalConjectures.Util.ProblemImports

private def kernelBool : Bool := false
private def execBool : Bool := true

@[implemented_by execBool]
def weirdBool : Bool := kernelBool

#eval weirdBool

example : weirdBool = true := by
  native_decide

example : False := by
  have h : weirdBool = true := by native_decide
  native_decide
