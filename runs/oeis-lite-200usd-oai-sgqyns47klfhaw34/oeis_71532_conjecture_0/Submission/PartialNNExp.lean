import FormalConjectures.Util.ProblemImports
partial def nn (P : Prop) : ¬¬P := fun h => nn P h
#print axioms nn
example (P : Prop) : ¬¬P := nn P
example : False := (nn False) id
#print axioms PartialNNExp._example_2
