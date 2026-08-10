import FormalConjectures.Util.ProblemImports
example : True := (fun (_ : False) => True.intro) lcProof
theorem ttrue : True := (fun (_ : False) => True.intro) lcProof
#print ttrue
#print axioms ttrue
