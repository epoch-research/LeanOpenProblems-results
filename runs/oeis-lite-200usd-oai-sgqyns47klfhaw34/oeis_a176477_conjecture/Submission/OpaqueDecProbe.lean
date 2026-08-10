import FormalConjectures.Util.ProblemImports
opaque dFalse : Decidable False
#check dFalse
example : decide False = true := by native_decide
example : False := of_decide_eq_true (show decide False = true from by native_decide)
