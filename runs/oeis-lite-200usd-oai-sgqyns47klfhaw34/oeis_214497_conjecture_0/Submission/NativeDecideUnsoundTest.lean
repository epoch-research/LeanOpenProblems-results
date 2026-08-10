import FormalConjectures.Util.ProblemImports

unsafe def runtimeTrue : Bool := true

@[implemented_by runtimeTrue]
def kernelFalse : Bool := false

#eval kernelFalse

theorem badNative : kernelFalse = true := by
  native_decide

#print axioms kernelFalse
#print axioms badNative
#print badNative
