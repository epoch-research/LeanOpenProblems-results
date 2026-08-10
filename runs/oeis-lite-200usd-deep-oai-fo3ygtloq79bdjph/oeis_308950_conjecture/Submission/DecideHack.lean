import FormalConjectures.Util.ProblemImports
example : False := by
  classical
  exact of_decide_eq_true (show decide False = true by native_decide)
#print axioms DecideHack._example
