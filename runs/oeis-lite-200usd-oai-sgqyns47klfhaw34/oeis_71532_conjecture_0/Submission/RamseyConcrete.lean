import FormalConjectures.Util.ProblemImports
#check Combinatorics.hypergraphRamsey_self
#print axioms Combinatorics.hypergraphRamsey_self
example : False := by
  have h := Combinatorics.hypergraphRamsey_self 0
  change Combinatorics.hypergraphRamsey 0 0 = 0 at h
  norm_num
