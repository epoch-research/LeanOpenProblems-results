import FormalConjectures.Util.ProblemImports
#check (inferInstance : Inhabited (Quot (fun (_ _ : False) => True)))
#check (default : Quot (fun (_ _ : False) => True))
#check Quot.out (default : Quot (fun (_ _ : False) => True))
example : False := Quot.out (default : Quot (fun (_ _ : False) => True))
#print axioms _example
