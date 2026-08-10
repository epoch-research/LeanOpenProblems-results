import FormalConjectures.Util.ProblemImports

def evilDecide (p : Prop) [Decidable p] : Bool := decide p
@[implemented_by fun _ _ => true]
def evilDecideImpl (p : Prop) [Decidable p] : Bool := evilDecide p

example : False := by
  have h : evilDecideImpl False = true := by native_decide
  native_decide -- maybe?
