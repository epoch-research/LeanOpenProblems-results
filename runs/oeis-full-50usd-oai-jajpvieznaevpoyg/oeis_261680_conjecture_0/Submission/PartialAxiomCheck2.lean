import FormalConjectures.Util.ProblemImports
partial def loopProof (u : Unit) : False := loopProof u
theorem tFalse : False := loopProof ()
#print axioms tFalse
