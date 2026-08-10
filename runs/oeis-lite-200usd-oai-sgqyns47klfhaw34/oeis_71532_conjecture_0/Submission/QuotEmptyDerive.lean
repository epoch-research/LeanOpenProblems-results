import FormalConjectures.Util.ProblemImports

def QE := Quot (fun _ _ : Empty => False)
deriving instance Nonempty for QE
example : False := Quot.out (Classical.choice (inferInstanceAs (Nonempty QE)))
#print axioms _example
