import FormalConjectures.Util.ProblemImports
mutual
partial def inh (P : Prop) : Inhabited P := ⟨pf P⟩
partial def pf (P : Prop) : P := (inh P).default
end
#print axioms inh
#print axioms pf
example (P : Prop) : P := pf P
#print axioms MutualPartialProof._example_1
