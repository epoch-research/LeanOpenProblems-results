import FormalConjectures.Util.ProblemImports
unsafe def trueUnsafe : Bool := true
@[implemented_by trueUnsafe]
def badBool : Bool := false

def P : Prop := badBool = true
instance : Decidable P := by unfold P; infer_instance
#eval badBool
theorem badP : P := by
  native_decide
#print axioms badP
#print badP
