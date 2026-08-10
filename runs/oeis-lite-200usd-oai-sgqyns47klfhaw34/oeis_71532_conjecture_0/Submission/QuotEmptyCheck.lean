import FormalConjectures.Util.ProblemImports

def QE := Quot (fun _ _ : Empty => False)
#check inferInstanceAs (Nonempty QE)
#check inferInstanceAs (Inhabited QE)
example : False := Quot.out (Classical.choice (inferInstanceAs (Nonempty QE)))
#print axioms _example
