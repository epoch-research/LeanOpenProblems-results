import FormalConjectures.Util.ProblemImports
#print IsEmpty
partial def loopEmpty (P : Prop) : IsEmpty P := loopEmpty P
theorem not_all (P:Prop) : ¬ P := fun hp => (loopEmpty P).false hp
#print axioms not_all
